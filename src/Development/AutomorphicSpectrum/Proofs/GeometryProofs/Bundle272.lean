module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeDegree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle264
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle061
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle072
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle261
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle229
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle269
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle270
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.component_data_hodge_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → ∃ G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G ∧ G.PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | exact GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks | (intros; apply GlobalTheory.CompanionTheory.Ar.gramAt_posDef_of_isFrameAt_blocks <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_system_hodge_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (d d' : MuFrameAt Hd w) (s s' : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (Γ Γ' : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → Or.IsSmallPart d s → Or.IsSmallPart d' s' → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s' τ) (Γ' τ)) → (∀ τ, (Γ τ).PosDef) → ‖valAt Dc.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ τ).det.re = ‖valAt Dc.y d'.u w‖ * (∏ k, ‖w ⟨k, d'.c k⟩‖ ^ Hd.aMu k) * ∏ τ, Real.sqrt (Γ' τ).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | exact GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.MuIndep.norm_indep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS

theorem _root_.GlobalTheory.T.holomorphic_extension_section_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | exact GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

theorem log_norm_det_scaled {E : Type} [Field E] (σ : E →+* ℂ) (rt : E) (d : ℕ) (hd : 0 < d)
    (hrt : rt ^ 2 = -(d : E)) (r : ℝ) (hr : 0 < r) (ε : ℤˣ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (hM : M.det ≠ 0) (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ k k', Γ k k' = (r : ℂ) * ((ε : ℤ) : ℂ) * σ (rt * M k k')) :
    Real.log ‖Γ.det‖ = (n : ℝ) * (Real.log r + Real.log d / 2) + Real.log ‖σ M.det‖ := by
  have hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M) := by
    ext k k'
    simp only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    ring
  have hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det := by
    rw [hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  have hε : ‖((ε : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hs : ‖σ rt‖ ^ 2 = d := by
    have h1 : σ rt ^ 2 = -(d : ℂ) := by
      rw [← map_pow, hrt]
      simp
    have h2 := congrArg norm h1
    simpa [norm_pow] using h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : ‖σ rt‖ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : (d : ℝ) = 0 := by simpa using hs.symm
    linarith
  have hlog : Real.log ‖σ rt‖ = Real.log d / 2 := by
    have h3 := congrArg Real.log hs
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hσM : σ M.det ≠ 0 := (map_ne_zero σ).2 hM
  have hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0 := by
    rw [norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]
    exact pow_ne_zero _ (mul_ne_zero hr.ne' hs0)
  rw [hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow,
    Real.log_mul hr.ne' hs0, hlog]

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz

theorem hasInfNorm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf
  classical
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ
  have hxli : LinearIndependent (𝓞 E) x := hloc.1
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hTdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hTne := hTdet hxli
  have hGe := (GlobalTheory.T.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  obtain ⟨hfram, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he
    hconst hxli hT hfr
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_extension_embedding_alg_closed k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s
  have hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a := fun a => DFunLike.congr_fun hs' a
  have hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom := by
    ext a
    exact hs'a (IntermediateField.inclusion hc a)
  have hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom =
      s.comp (IntermediateField.inclusion (hM b)).toRingHom := by
    intro b
    ext a
    exact hs'a (IntermediateField.inclusion (hM b) a)

  let y' : Sp ℂ ⟶ Xo.XF c := spMap s' ≫ X.y
  have hy' : under y' = spMap s' ≫ under X.y := Category.assoc _ _ _
  obtain ⟨⟨v', hv'⟩, hvI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hy'
  obtain ⟨⟨w', hw'⟩, hwI⟩ := GlobalTheory.T.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'
  have hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hβ]
      simp only [y', Category.assoc, hfram.1]
      simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
    · rintro _ ⟨u, rfl⟩
      apply hfram.2.1
      exact ⟨(spMap s') u, by simp [y']⟩
    · rw [← hβ, RingHom.comp_assoc]
      exact (hvI v' hv').1 hfram.2.2.1
    · rw [← hβ, RingHom.comp_assoc]
      exact (hwI w' hw').1 hfram.2.2.2
  have hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false := by
    simp only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]
    exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hΓ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n
    (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)
  have hΔ := GlobalTheory.T.cm_pack_period_product E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q
    (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)
  have hmain := hinf y' v' w' _ _ hfram' hΓ hΔ
  rw [hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw'] at hmain

  have hblock : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    · exact (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2
    · rfl
  have hdet1 : (gramE (FU.Di i) x).det =
      (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
  have hdet2 : (gramE (FU.Di i) x).det =
      T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    have hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']
  have hconjne : IsCMField.complexConj E T.det ≠ 0 := by
    simpa using hTne
  have hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    rw [← hdet1, hdet2]
    exact mul_ne_zero (mul_ne_zero hTne hGe) hconjne
  have hG1 := left_ne_zero_of_mul hG
  have hG2 := right_ne_zero_of_mul hG

  let σ : E →+* ℂ := s'.comp (X.β.comp (tauE c τ))
  let σ' : E →+* ℂ := s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))
  have hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖ := by
    intro a
    have h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a) := by
      apply Subtype.ext
      change ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    have h2 : σ' a = σ (IsCMField.complexConj E a) := by
      simp only [σ', σ, RingHom.comp_apply, h1]
    rw [h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]
  have hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hlΓ := log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true)
    (gramE (FU.Di i) (x ∘ Sum.inl)) hG1
    (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) *
      s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)
  have hlΔ := log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false)
    (gramE (FU.Di i) (x ∘ Sum.inr)) hG2
    (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) *
      s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun _ _ => rfl)
  rw [hσ'] at hlΔ

  have hz := GlobalTheory.T.curve_z_ne_zero E H _ (Z true)
  have hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    apply mul_right_cancel₀ (pow_ne_zero D.p hz)
    rw [hval, ← hrz]
    ring
  have hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) =
      IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
    Subtype.ext hval2
  have hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    have := congrArg s' hK
    rw [map_mul, map_mul, hs'a] at this
    exact this
  have hφ0 : s' (φ X.K X.y v w) ≠ 0 := (map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)
  have hσT : σ T.det ≠ 0 := (map_ne_zero σ).2 hTne
  have hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := (map_ne_zero σ).2 hG2
  have hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0 := (map_ne_zero σ).2 hG1
  have hσGe : σ (gramE (FU.Di i) e).det ≠ 0 := (map_ne_zero σ).2 hGe
  have hsr : s r ≠ 0 := (map_ne_zero s).2 hr
  have hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ =
      Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT),
      ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]
  have hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ =
      2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖ := by
    have h1 := congrArg σ (hdet1.symm.trans hdet2)
    rw [map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT),
      Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)] at h3
    linarith
  have hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) =
      σ (gramE (FU.Di i) e).det :=
    (DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm
  rw [hlast]
  rw [hlΓ, hlΔ] at hmain
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.InfPlace
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg

theorem finite_fieldRange {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    FiniteDimensional ℚ τ.toRatAlgHom.fieldRange :=
  (AlgEquiv.ofInjectiveField τ.toRatAlgHom).toLinearEquiv.finiteDimensional

theorem const_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) →
    IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ →
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧
      (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ hty hrt hmem hline he hconst
  obtain ⟨P, hP, x, hx, X, v, w, hk, hloc, hfr⟩ :=
    GlobalTheory.T.exists_cm_period_embedding E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ τ.toRatAlgHom.fieldRange (finite_fieldRange τ) hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, -, hdet, -⟩ := GlobalTheory.T.exists_transition_matrix_gram E H (FU.Di i) _ x e hcard he
  have hT0 : T.det ≠ 0 := hdet hloc.1
  have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
    (GlobalTheory.T.pure_type_lattices_orthogonal E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
  have hG0 := (GlobalTheory.T.local_basis_gram_det_log_norm E H (FU.Di i) D.p D.q x ⟨2, Nat.prime_two⟩ hloc horth).1
  obtain ⟨hfm, hval⟩ := GlobalTheory.T.cm_pack_pure_frame_open E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt hmem hline he
    hconst hloc.1 hT hfr
  have hφ : φ X.K X.y v w ≠ 0 := hline.ne X.K X.β X.y v w hfm
  have hmemK : ∀ t : E, τ t ∈ X.K := fun t => hk (τ.toRatAlgHom.mem_fieldRange.2 ⟨t, rfl⟩)
  set G := gramE (FU.Di i) (x ∘ Sum.inr) with hGdef
  let a : X.K := ⟨τ T.det, hmemK _⟩
  let b : X.K := ⟨τ G.det, hmemK _⟩
  have ha : a ≠ 0 := fun h => hT0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hb : b ≠ 0 := fun h => hG0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hbC : τ G.det ≠ 0 := (map_ne_zero τ).2 hG0
  refine ⟨X.K, inferInstance, φ X.K X.y v w * a / b, X.hc, X.hM, div_ne_zero (mul_ne_zero hφ ha) hb, ?_⟩
  have hcoe : ((φ X.K X.y v w * a / b : X.K) : ℂ) = ((φ X.K X.y v w : X.K) : ℂ) * τ T.det / τ G.det := rfl
  rw [hcoe]
  field_simp
  linear_combination hval

end GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.cm_pack_pure_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (τ : E →+* ℂ) (ℓ : Nat.Primes) (j : X.K →+* ℂ_[ℓ]) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsLocBasis (𝓞 E) ℓ x → X.IsCMFrame τ hx v w → ∃ (V : Subring X.K) (_ : IsDiscreteValuationRing V) (_ : IsFractionRing V X.K) (T : SAB H (Sp V)) (m'' : SABMap X.t T (spMap (algebraMap V X.K))) (δ δ' : X.K) (v' : Vecs X.y D.p) (w' : Vecs X.y D.q), (∀ a : X.K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V X.K).range) ∧ δ ≠ 0 ∧ δ' ≠ 0 ∧ Real.log ‖j δ‖ = logIdeal ((j.comp (X.β.comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (X.β (tauE c τ (H.rt : E)))‖ ∧ Real.log ‖j δ'‖ = Real.log ‖j δ‖ ∧ (∀ a, IsComb ((δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K)) a) v (v' a)) ∧ (∀ a, IsComb ((δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) a) w (w' a)) ∧ IsFramed (Set.range X.y) τ X.β X.y v' w' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c τ)) v' ∧ IsIntFrame X.m m'' (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | exact GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)


theorem _root_.GlobalTheory.T.hodge_comp_descent_fifth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (hv : IsBlockMap bk (blkV bk bx)) (r : CMType H × Fin (D.p + D.q)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (A₀ : HermLine J₀) (T : HermLine J), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → NormPull Fl₀ Fl i h → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ (z ≫ h) a r → ValAt 𝔐.ξ z (i a) r) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → (∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, 𝔐.Interior z → 𝔐₀.Interior (z ≫ h)) → e ≠ 0 → A₀.a = a₀ → T.a = a - pullDeg bk a₀ → IsRatio 𝔐.ξ y y₀ bk bx i a a₀ e e₀ T.h → Fl₀.IsHodgeLine r e₀ A₀ → Fl.IsHodgeLine r e ((pullHerm hv A₀).tensor T) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | exact GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.isHodgeLine_pull_tensor <;> assumption)
end
