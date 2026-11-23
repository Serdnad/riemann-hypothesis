module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle037
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle068
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OneMulConjFracOneEqInvDifferent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem two_mul_sub_one_sq_of_ringHom (τ : OK H →+* ℂ) : (2 * τ (wK H) - 1) ^ 2 = -(H.d : ℂ) := by
  have h : (2 * wK H - 1) ^ 2 = -(H.d : OK H) := by
    apply Subtype.ext
    have e : 2 * H.w0 - 1 = H.rt := by rw [H.two_weight_eq_one_add_root]; ring
    have := H.rt_sq
    rw [← e] at this
    have e2 : ((2 : OK H) : 𝓞 E) = 2 := rfl
    simpa [wK, e2] using this
  have := congrArg (fun x : OK H => τ x) h
  set_option synthInstance.maxHeartbeats 200000 in
    simpa only [map_pow, map_sub, map_mul, map_ofNat, map_neg, map_natCast, map_intCast, map_one] using this

theorem exists_hermitianPairing_eq_im_mul_pureType {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ω : ℂ} {x : D.La} (hx : x ∈ PureType.lat hP (2 * ω - 1)) (h0 : x ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ((D.EF (H.w0 • x) x : ℤ) : ℝ) = ω.im * r := by
  obtain ⟨Hm, hH, hpos, hEF⟩ := hP.2.2.2.2
  have hw0 : Pe (H.w0 • x) = ω • Pe x := by
    have e : (2 : ℂ) • Pe (H.w0 • x) = (2 : ℂ) • ω • Pe x := by
      rw [two_smul, ← map_add (f := _), ← add_smul, ← two_mul, H.two_weight_eq_one_add_root, add_smul, one_smul, map_add (f := _),
        PureType.period_rt_smul hP hx]
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    exact smul_right_injective _ two_ne_zero e
  have hne : Pe x ≠ 0 := fun h => h0 (hP.2.1 (by rw [h, map_zero]))
  refine ⟨_, hpos _ hne, ?_⟩
  have := PureTypeVector.hermForm_smul_smul Hm ω 1 (Pe x) (Pe x)
  rw [one_smul] at this
  rw [← hEF, hw0, this]
  simp [PureTypeVector.hermForm_self_im hH]

theorem exists_isFam_complex : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (ω : ℂ) (C : Ell H ℂ ω) (u₀ : HolUnif C.P.A C.P.L C.P.g) (c : ℂ) (T : PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t (FU.u i Pe)) (ε : ℤˣ) (h : (FU.Di i).La → (FU.Di i).La → OK H), PureType.IsThetaUnif u₀ → c ≠ 0 → PureType.IsQuadLattice u₀.Λ H.d c → 0 < ((ε : ℤ) : ℝ) * ω.im → IsKForm (FU.Di i) ε h →
  ∃ ψ : PureType.lat hP (2 * ω - 1) → (C.P.A ⟶ T.t.G), IsFam C T h _ ψ ∧ ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hT hL E _ _ _ H D l Xo g ty FU i Pe hP ω C u₀ c T m ε h hu hc hΛ hε hh
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.cmCurve_lie_character_of_adjoinGenerator E H ℂ ω C
  have hρ : (2 * ω - 1) ^ 2 = -(H.d : ℂ) := hτ ▸ two_mul_sub_one_sq_of_ringHom τ
  obtain ⟨φ, hφ, hφe⟩ := PureType.exists_isHomFamily_complex hT hL.weil FU i hP m u₀ C.dim hu hc hΛ hρ
  refine ⟨φ, GlobalTheory.T.isCMPairingFamily_of_polarisationDiagonal_complex hT hL E H ω C _ ε h T _ φ hh (fun x hx h0 => ?_) (hφ _ (C.basis.1 0)), fun a z => ?_⟩
  · obtain ⟨r, hr, e⟩ := exists_hermitianPairing_eq_im_mul_pureType hP hx h0
    have : (0 : ℝ) < ((ε : ℤ) : ℝ) * ((FU.Di i).EF (H.w0 • x) x : ℤ) := by
      rw [e, ← _root_.mul_assoc]
      exact mul_pos hε hr
    exact_mod_cast this
  · rw [Over.comp_left, Category.assoc]
    exact hφe a z

end GlobalTheory.CM
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllExists

theorem isQuadLattice_of_linear {g g' : ℕ} (hg : g = 1) (hg' : g' = 1) {Λ : Submodule ℤ (Fin g → ℂ)}
    {Λ' : Submodule ℤ (Fin g' → ℂ)} (hd : DiscreteTopology Λ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    (hF : ∀ z, z ∈ Λ ↔ F z ∈ Λ') {d : ℕ} {c : ℂ} (hc : c ≠ 0) (h : PureType.IsQuadLattice Λ' d c) :
    ∃ c' : ℂ, c' ≠ 0 ∧ PureType.IsQuadLattice Λ d c' := by
  subst hg hg'
  obtain ⟨a, ha⟩ : ∃ a : ℂ, ∀ z, F z = fun _ => a * z 0 := ⟨F (fun _ => 1) 0, fun z => by
    have e : z = z 0 • fun _ => (1 : ℂ) := by
      funext i
      fin_cases i
      simp
    funext i
    fin_cases i
    conv_lhs => rw [e, map_smul]
    simp [mul_comm]⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    have ht : (Λ : Set (Fin 1 → ℂ)) = Set.univ := Set.eq_univ_of_forall fun z => (hF z).2 (by
      rw [ha]
      simp only [zero_mul]
      exact Λ'.zero_mem)
    have h1 : IsDiscrete (Λ : Set (Fin 1 → ℂ)) := ⟨hd⟩
    rw [ht, isDiscrete_univ_iff] at h1
    have := (isClopen_discrete ({0} : Set (Fin 1 → ℂ))).eq_univ ⟨0, rfl⟩
    have h2 : (1 : Fin 1 → ℂ) ∈ ({0} : Set (Fin 1 → ℂ)) := this ▸ Set.mem_univ _
    exact one_ne_zero h2
  refine ⟨c / a, div_ne_zero hc ha0, fun z => ?_⟩
  rw [hF, h, ha]
  refine exists₂_congr fun m n => ⟨fun e => ?_, fun e => ?_⟩
  · funext i
    fin_cases i
    have := congrFun e 0
    field_simp
    field_simp at this
    simpa [mul_comm a] using this
  · funext i
    rw [e]
    field_simp

theorem isQuadLattice_of_isGrpPullback (hU : ThetaUnifAV) (hL : Out.Laws) {R : Type} [CommRing R]
    (P : Out.PolAV (Sp R)) (hg : P.g = 1) (σ : R →+* ℂ) {d : ℕ}
    (h : ∀ (Q : Out.PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left), IsPolFibre σ P Q φ → ∀ u : HolUnif Q.A Q.L Q.g,
      ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c)
    (Q : Out.PolAV (Sp ℂ)) (hQ : Q.g = 1) (φ : Q.A.left ⟶ P.A.left) (hφ : IsGrpPullback Q.A P.A (spMap σ) φ)
    (u : HolUnif Q.A Q.L Q.g) : ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ d c := by
  obtain ⟨Q₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange σ P
  obtain ⟨rig, hrig⟩ := Q₀.rigid
  obtain ⟨u₀, -, -, -, -, -, t₁, t₂, -⟩ := hU Q₀ rig hrig
  obtain ⟨c, hc, hΛ⟩ := h Q₀ φ₀ h₀ u₀
  obtain ⟨f, hf, ef⟩ := NormHom.exists_monHom_lift hφ h₀.2.1 (𝟙 P.A)
  obtain ⟨F, hF, hF', -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q₀.A Q.isAb Q₀.isAb Q.L Q₀.L Q.g Q₀.g u u₀ t₁ t₂ f hf
  refine isQuadLattice_of_linear hQ (h₀.1.trans hg) u.discrete F (fun z => ⟨hF' z, fun hz => ?_⟩) hc hΛ
  rw [← u₀.ker, hF] at hz
  rw [← u.ker]
  apply NormHom.push_inj hφ
  have e := NormHom.push_comp hφ h₀.2.1 ef (u.ex z)
  rw [hz, map_one, Category.comp_id] at e
  rw [map_one, e]

theorem exists_ell_pos (hC : CMCurve) (hU : ThetaUnifAV) (hL : Out.Laws) (hX : HomExtDvr) {E : Type} [Field E]
    [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] {χ : DirichletCharacter ℂ H.d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ),
      ((ω : M) : ℂ) = (1 + Complex.I * √H.d) / 2 ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧
      C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) -
        deriv χ.LFunction 1 / χ.LFunction 1 := by
  have hm := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) (by omega)
  obtain ⟨M, _, w, P, v, hw, hg, hv, ⟨P₀, φ, v₀, W, hφ, hv₀, hb₀, hW, hWW, hWv⟩, hΛ, n, hn0, hn, hx, -⟩ :=
    chowla_selberg_lie_lines hC (by omega) H.d_prime.squarefree (by omega) h2 hr hχ
  have := P₀.isAb.comm
  have := P.isAb.comm
  obtain ⟨a₀, ha₀, -⟩ := GlobalTheory.T.exists_cmAdjoin_action_of_equation E H _ P₀.A W hW hWW
  obtain ⟨a, ha⟩ := exists_oAct_extend_dedekind hX (𝓞 M) M (OK H) P.A P₀.A φ P.isAb hφ.2.1 a₀
  have hvt : IsTangent v := hv.1 0
  have := a.hom (wK H)
  obtain ⟨c, hc, -⟩ := hv.2 _ (HomLinear.isTangent_comp (a.act (wK H)) hvt)
  obtain ⟨ω, rfl⟩ : ∃ ω, c = ![ω] := ⟨c 0, by funext i; fin_cases i; rfl⟩
  have hc₀ := (lieComb_baseChange _ _ (algebraMap (𝓞 M) M) P.A P₀.A φ hφ.2.1 1 ![v] _ ![ω] ![v₀] (v₀ ≫ W)
    (fun j => by fin_cases j; exact hv₀) hc).1 (NormHom.isVecOver_comp hv₀ (ha₀ ▸ ha (wK H)))
  have hω : (ω : M) = w := congrFun ((hb₀.2 _ (HomLinear.isTangent_comp W (hb₀.1 0))).unique hc₀ hWv) 0
  have hσ : Function.Injective ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) :=
    (algebraMap M ℂ).injective.comp (IsFractionRing.injective (𝓞 M) M)
  obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.T.exists_normalized_symmetric_ample_lb hL (𝓞 M) P (a.act (wK H)) (a.act (EllConj.barK H (wK H)))
    (a.hom _) (a.hom _) (by rw [← a.add, add_comm, EllConj.barK_wK_add, a.one])
    (GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P a hσ hg _ _ rfl)
  let P' : Out.PolAV (Sp (𝓞 M)) := ⟨P.A, P.isAb, P.g, P.smoothDim, L', h₁, h₂, h₃, h₄, h₅⟩
  have key : ∀ (s : M →+* ℂ) r, IsLieNormSq P' v (s.comp (algebraMap (𝓞 M) M)) r → r = n s := fun s r h => by
    have h1 : IsLieComb ![(1 : 𝓞 M)] ![v] (v ≫ 𝟙 P.A) := by
      rw [LieComb.isLieComb_iff_tanExp, Category.comp_id]
      have e : (![1] : Fin 1 → 𝓞 M) = Pi.single 0 1 := by
        funext i
        fin_cases i
        simp
      rw [e]
      exact (LieComb.tanExp_single hv.1 0).symm
    have e := NormHom.lieNormSq_comp hU hL (𝓞 M) P P' (𝟙 P.A) (𝟙 P.A) v 1 _ (n s) r inferInstance inferInstance h₆ hvt
      h1 ((hn s _).2 rfl) (by rwa [Category.comp_id])
    simpa using e
  refine ⟨M, inferInstance, ω, ⟨P', hg, a, v, hv, hc, GlobalTheory.T.cmAction_polarisedCurve_adjoint_conj hU hL E H (𝓞 M) _ P' a hσ hg, h₇⟩, -meanLog M n,
    hω ▸ hw, fun Q ψ hψ u => ?_, ⟨n, fun s => ⟨hn0 s, fun r => ⟨key s r, fun e => ?_⟩⟩, rfl⟩, hx⟩
  · refine isQuadLattice_of_isGrpPullback hU hL P hg _ (fun Q ψ hψ u => ?_) Q (hψ.1.trans hg) ψ hψ.2.1 u
    obtain ⟨c, hc, h⟩ := hΛ Q ψ hψ u
    rw [hw] at h
    exact ⟨c, hc, h⟩
  · obtain ⟨r', hr'⟩ := exists_isLieNormSq hU hL.polBaseChange P' hvt (s.comp (algebraMap (𝓞 M) M))
    rwa [e, ← key s r' hr']

theorem exists_ell : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ ρ : ℂ, ρ ^ 2 = -(H.d : ℂ) → ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : Ell H (𝓞 M) ω) (x : ℝ), 2 * ((ω : M) : ℂ) - 1 = ρ ∧ C.IsPrincipalAt ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) ∧ C.HasPeriod x ∧ (x : ℂ) = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √H.d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  intro hC hU hL hX E _ _ _ H _ χ hχ ρ hρ
  obtain ⟨M, _, ω, C, x, hω, hp, hx, hv⟩ := exists_ell_pos hC hU hL hX H hχ
  have e : ρ ^ 2 = (Complex.I * √H.d) ^ 2 := by
    rw [hρ, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with rfl | rfl
  · exact ⟨M, inferInstance, ω, C, x, by rw [hω]; ring, hp, hx, hv⟩
  · obtain ⟨a, -, h₁, h₂, h₃⟩ := EllConj.exists_conj_action E H (𝓞 M) ω C
    refine ⟨M, inferInstance, 1 - ω, ⟨C.P, C.dim, a, C.v, C.basis, h₁, h₂, h₃⟩, x, ?_, hp, hx, hv⟩
    have : (((1 - ω : 𝓞 M) : M) : ℂ) = 1 - ((ω : M) : ℂ) := by simp
    rw [this, hω]
    ring

end GlobalTheory.CM.EllExists
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.commutatorPairings_eq_of_cubeLBPairingIso : Out.Laws → ∀ (R : Type) [CommRing R] [IsDedekindDomain R] [CharZero R] (X Y A B : Out.PolAV (Sp R)) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A), IsMonHom f₁ → IsMonHom f₂ → IsMonHom g₁ → IsMonHom g₂ → LamEq A.L f₁ f₂ B.L g₁ g₂ → ∀ (T : Over (Sp R)) (k : ℕ) (x : T ⟶ X.A) (y : T ⟶ Y.A) (c : Γ(T.left, ⊤)ˣ), 0 < k → x ^ k = 1 → y ^ k = 1 → (Out.WeilIs A.A A.L k (x ≫ f₁) (y ≫ f₂) c ↔ Out.WeilIs B.A B.L k (x ≫ g₁) (y ≫ g₂) c) := by
  first | exact @GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | exact GlobalTheory.PairingScheme.weilIs_iff_of_lamEq | (intros; apply GlobalTheory.PairingScheme.weilIs_iff_of_lamEq <;> assumption)
end
