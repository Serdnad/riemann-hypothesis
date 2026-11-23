module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle146
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImInvIsHermitian
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle075
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle149
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle109
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle079
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

namespace SharpObj

theorem omegaStd_sum_smul {h : ℕ} {I : Type} [Fintype I] (x : Fin h ⊕ Fin h → ℤ) (c : I → ℤ)
    (y : I → Fin h ⊕ Fin h → ℤ) : omegaStd x (∑ v, c v • y v) = ∑ v, c v * omegaStd x (y v) := by
  simp only [omegaStd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_act {h : ℕ} (G A : Matrix (Fin 8) (Fin 8) ℤ) (x : Fin 8 → Fin h ⊕ Fin h → ℤ) :
    ∑ u, ∑ v, G u v * omegaStd (x u) (∑ v', A v v' • x v') = ∑ u, ∑ v, (G * A) u v * omegaStd (x u) (x v) := by
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [omegaStd_sum_smul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * Complex.I * (n : ℂ)) = (-1) ^ n := by
  rw [_root_.mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem hermForm_eq_sum {g h : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (H₀ : Matrix (Fin h) (Fin h) ℂ)
    (G : Matrix (Fin 8) (Fin 8) ℤ) (R : Fin 8 → ((Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ))) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤)
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm z w).im = ∑ i, ∑ j, (G i j : ℝ) * (hermForm H₀ (R i z) (R j w)).im) (z w) :
    hermForm Hm z w = ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w) := by
  refine sub_eq_zero.1 (form_ext s hs
    (fun z w => hermForm Hm z w - ∑ i, ∑ j, (G i j : ℂ) * hermForm H₀ (R i z) (R j w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [hermForm, map_add (f := _), add_dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  · intro z w w'
    simp only [hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, mul_add, Finset.sum_add_distrib]
    ring
  · intro c z w
    simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, mul_sub, Finset.mul_sum, mul_left_comm c]
  · intro c z w
    simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_sub,
      Finset.mul_sum, Complex.star_def, Complex.conj_ofReal, mul_left_comm (c : ℂ)]
  · intro z hz w hw
    simp [h0 z hz w hw, Complex.im_sum]

end SharpObj


open SharpObj in
theorem sharpClass_of_unif : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ (t : TObj g k J b (spMap em)) (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) → (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) → (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → SharpClass W a bas em t := by
  intro laws laws2 hc hT o _ g k J b em w w' h W a bas σ EF _ _ hw _ hEF t τ m Q Hm ⟨hs, hp⟩ hm hQ
    ⟨_, _, Qspan, _, _, hQim⟩ ⟨u, χ', hAH, hΛ, hχ, hpt, hact⟩
  obtain ⟨Ef₀, hEf₀, hbij⟩ := exists_form hs hp
  obtain ⟨P₀, u₀, χ₀, hg, hΛ₀, hAH₀, -, -⟩ := principalTorus_algebraic h _ (imInv τ) Ef₀ (per_lattice hs hp).2.1
    (per_lattice hs hp).2.2 (imInv_isHermitian hp) (imInv_pos hp) hEf₀ hbij
  subst hg
  let R : Fin 8 → (Fin g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ) := fun i => LinearMap.funLeft ℂ ℂ fun j => σ (i, j)
  have hRQ : ∀ i x, R i (Q x) = per τ (x i) := fun i x => funext fun j => hQ x i j
  have hmem : ∀ x, per τ x ∈ u₀.Λ := fun x => hΛ₀ ▸ ⟨x, rfl⟩
  have hΛ' : ∀ z, z ∈ u.Λ ↔ ∀ i, (fun j => z (σ (i, j))) ∈ u₀.Λ := fun z => by
    rw [hΛ, hΛ₀]
    constructor
    · rintro ⟨x, rfl⟩ i
      exact ⟨x i, (hRQ i x).symm⟩
    · intro H
      choose x hx using H
      refine ⟨x, funext fun c => ?_⟩
      obtain ⟨⟨i, j⟩, rfl⟩ := σ.surjective c
      exact (hQ x i j).trans (congrFun (hx i) j)
  obtain ⟨pr, hpr, hpru, hprod⟩ := exists_proj laws laws2 hc hT t.pol P₀ u u₀ σ hΛ'
  change Fin 8 → (t.A ⟶ P₀.A) at pr
  change ∀ i, IsMonHom (pr i : t.A ⟶ P₀.A) at hpr
  change ∀ (T : Over (Sp ℂ)) (y : Fin 8 → (T ⟶ P₀.A)), ∃! x : T ⟶ t.A, ∀ i, x ≫ pr i = y i at hprod
  change ∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i at hpru
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hk (by simp [e])
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hWeil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm laws laws2 hc hT P₀ u₀ _ χ₀ hAH₀
  obtain ⟨c, φ, hφ, hcP, ⟨wP, hwP⟩, hlev⟩ := GlobalTheory.T.exists_siegPre_iso_of_polAV laws hc o ℂ em P₀.g k b.ζ (Units.map (em : o →* ℂ) b.ζ) P₀
    (fun x => u₀.ex ((k : ℂ)⁻¹ • per τ (m x))) rfl hk rfl
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em))
    (fun x y => by rw [map_add (f := _), map_add (f := _), smul_add, u₀.ex_add])
    (fun x => by
      rw [← ex_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul, u₀.ker]
      exact hmem _)
    (fun x y => hWeil k ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ _ hk0 (by
      have e : Ef ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩ = omegaStd (m x) (m y) := by
        have := hEf ⟨_, hmem (m x)⟩ ⟨_, hmem (m y)⟩
        rw [im_hermForm_per hs hp] at this
        exact_mod_cast this
      rw [e, hm]
      simp))
  have hform : ∀ z z', hermForm Hm z z' =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm (imInv τ) (R i z) (R j z') :=
    hermForm_eq_sum Hm (imInv τ) (W + W.transpose) R _ Qspan (by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      simp only [hQim, hEF, hRQ, im_hermForm_per hs hp, Int.cast_sum, Int.cast_mul])
  have hchi : ∀ l : u.Λ, χ' l = Complex.exp (Real.pi * Complex.I *
      ∑ i, ∑ j, (W i j : ℂ) * ((hermForm (imInv τ) (R i l) (R j l)).im : ℂ)) := fun l => by
    obtain ⟨x, hx⟩ := (hΛ l).1 l.2
    rw [hχ x l hx.symm, hEF, form_act, hw, ← exp_pi_I_int, ← hx]
    simp [hRQ, im_hermForm_per hs hp]
  have hL := GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt laws laws2 hc hT W t.pol u Hm χ' P₀ u₀ _ χ₀ pr R hAH hAH₀ hpru hform hchi
  letI := P₀.isAb.comm
  haveI := hpr
  refine ⟨c, hcP, fun i => pr i ≫ φ.inv, fun i => inferInstanceAs (IsMonHom (pr i ≫ φ.inv)), fun T y => ?_, ?_, fun j i => ?_, fun i v => ?_⟩
  · simp only [← Category.assoc, Iso.comp_inv_eq]
    exact hprod T fun i => y i ≫ φ.hom
  · have hLam : (abelian₂ P₀.A P₀.L).IsLB := DVR.linComb_isLB _ P₀.isLB _ _
    refine LBIso.trans t.isLB (DVR.linComb_isLB _ hLam _ _) (DVR.linComb_isLB _ c.isLB _ _) hL (LBIso.symm ?_)
    have := iso_linComb ((isGen_iff wP).1 hwP) (K := Fin 8 × Fin 8)
      (fun uv => (lift (pr uv.1 ≫ φ.inv) (pr uv.2 ≫ φ.inv)).left) (fun uv => W uv.1 uv.2)
    simp only [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] at this
    exact this
  · obtain ⟨F, hF, hFa⟩ := hact j
    haveI := t.hom j
    have hRF : ∀ z, R i (F z) = ∑ v, a j i v • R v z := fun z => by
      have : ((R i ∘ₗ F).restrictScalars ℝ) = (∑ v, a j i v • R v).restrictScalars ℝ :=
        LinearMap.ext_on_range Qspan fun x => by
          rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.comp_apply, hF, hRQ,
            LinearMap.sum_apply]
          simp only [LinearMap.smul_apply, hRQ]
          exact (map_sum (per τ) _ _).trans (Finset.sum_congr rfl fun v _ => map_zsmul (per τ) _ _)
      simpa using LinearMap.congr_fun this z
    have e1 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ t.act j ≫ pr i := fun z => by
      rw [hpru, hFa, Category.assoc]
    have e2 : ∀ z, u₀.ex (R i (F z)) = u.ex z ≫ ∏ v, pr v ^ a j i v := fun z => by
      rw [hRF, ex_sum, PowMatrixLinear.comp_prod]
      simp only [ex_zsmul, hpru, GrpObj.comp_zpow]
    have e : t.act j ≫ pr i = ∏ v, pr v ^ a j i v :=
      hom_ext_of_lin laws laws2 hc hT t.pol P₀ u u₀ (R i ∘ₗ F) _ _ e1 e2
        (inferInstanceAs (IsMonHom (t.act j ≫ pr i)))
    rw [← Category.assoc, e, PowMatrixLinear.prod_comp]
    simp only [GrpObj.zpow_comp]
    exact (List.prod_ofFn).symm
  · rw [Over.comp_left, hpt, ← Over.comp_left, ← Category.assoc, ← hpru, map_smul, hRQ, ← hlev, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.GenericDim

open GlobalTheory.CoordChart

theorem exists_secCoord_field {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {σ : Type} (th : σ → M.Sec)
    {K : Type} [Field K] (x : Sp K ⟶ X) : ∃ v, SecCoord M th x v := by
  let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
  have h : x p₀ ∈ ⨆ i, M.U i := by rw [hM.cover]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  have : y = p₀ := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [this]; exact hk

theorem exists_common_field {R L : Type} [CommRing R] [CommRing L] [IsDomain L] (q : Ideal R) [q.IsPrime]
    (φ : R →+* L) (h : RingHom.ker φ = q) :
    ∃ (K : Type) (_ : Field K) (lam : L →+* K) (j : FractionRing (R ⧸ q) →+* K), Function.Injective lam ∧
      j.comp ((algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)) = lam.comp φ := by
  have hl := IsFractionRing.injective L (FractionRing L)
  have hχ : Function.Injective ((algebraMap L (FractionRing L)).comp (Ideal.Quotient.lift q φ fun a ha => h.ge ha)) :=
    hl.comp ((Ideal.injective_lift_iff fun a ha => h.ge ha).2 h)
  refine ⟨FractionRing L, inferInstance, algebraMap L (FractionRing L),
    IsFractionRing.lift (A := R ⧸ q) (K := FractionRing (R ⧸ q)) hχ, hl, ?_⟩
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, IsFractionRing.lift_algebraMap hχ, RingHom.comp_apply,
    RingHom.comp_apply]
  exact congrArg _ (Ideal.Quotient.lift_mk q φ _)

theorem exists_extension {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) [IsOpenImmersion x]
    (hx : x ≫ Y.s = spMap β) (q : Ideal R) [q.IsPrime] (hmin : q ∈ minimalPrimes R)
    (y : R →+* FractionRing (R ⧸ q)) (hy : y = (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q))
    (v : Ix g (N' ^ 2) → FractionRing (R ⧸ q)) (hv : SecCoord Y.de Y.th (spMap y ≫ x) v)
    (P : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (hP : P.IsPrime) (hI : I ≤ P)
    (hle : P ≤ RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) v)) :
    ∃ (K : Type) (_ : Field K) (j : FractionRing (R ⧸ q) →+* K) (u : Kˣ),
      RingHom.ker (MvPolynomial.eval₂Hom (j.comp (y.comp β)) (fun a => u * j (v a))) = P := by
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc _ _ _ _ h3 hv
  set ev := MvPolynomial.eval₂Hom (y.comp β) v with hev
  let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* FractionRing (R ⧸ q) :=
    Ideal.Quotient.lift P ev fun a ha => hle ha
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let L := Localization.AtPrime (RingHom.ker e)
  have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
  let ψ : L →+* FractionRing (R ⧸ q) := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
  let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
  have hπ : ∀ F, ψ (π F) = ev F := fun F => by
    simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
    conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
    rfl
  have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
  have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
    intro l hl
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
    intro ha
    apply hl
    change ψ (IsLocalization.mk' L a s) = 0
    rw [IsLocalization.lift_mk'_spec, mul_zero]
    exact ha
  have hw : ∀ a, ψ (π (MvPolynomial.X a)) = v a := fun a => by rw [hπ]; simp [hev]
  have hβ : ψ.comp (π.comp MvPolynomial.C) = y.comp β := by ext t; simp [hπ, hev]
  have hL : InMM n N' I (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) := by
    refine ⟨fun F hF => by rw [hπe, hπ0]; exact hI hF, fun r hr a => ?_⟩
    obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨c, fun hm => hr.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa only [Ideal.mem_bot] using hc
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L _ _ hL
  have h4 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts _ _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, hv⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp (FractionRing (R ⧸ q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing (R ⧸ q)))
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal _)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa only [Ideal.mem_bot] using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  have hφy : ψ.comp φ = y := sp_inj (by rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq])
  have hφβ : φ.comp β = π.comp MvPolynomial.C := sp_inj (by rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1])
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    rw [hy, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hk1 : RingHom.ker φ ≤ q := fun r hr => by
    rw [RingHom.mem_ker] at hr
    rw [← hy0, ← hφy, RingHom.comp_apply, hr, map_zero]
  have hk2 : q ≤ RingHom.ker φ := hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ hk1
  haveI : IsDomain L := IsLocalization.isDomain_localization (RingHom.ker e).primeCompl_le_nonZeroDivisors
  obtain ⟨K, _, lam, j, hl, hj⟩ := exists_common_field q φ (le_antisymm hk1 hk2)
  rw [← hy] at hj
  have h6 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 _ j
  have h7 := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 _ lam
  rw [← Category.assoc, sp_comp, hj, ← sp_comp, Category.assoc, hz] at h6
  obtain ⟨u, hu'⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 _ h7
  refine ⟨K, inferInstance, j, u, ?_⟩
  ext F
  rw [RingHom.mem_ker, ← hπ0, ← map_eq_zero_iff lam hl, ← hπe, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hj,
    RingHom.comp_assoc, hφβ, MvPolynomial.coe_eval₂Hom, ← funext hu']
  rfl

theorem le_ringKrullDim_of_independent {o : Type} [CommRing o] [IsDomain o] {R : Type} [CommRing R] [Algebra o R]
    [Algebra.FiniteType o R] {d : ℕ}
    (h : ∀ (q : Ideal R) [q.IsPrime], q ∈ minimalPrimes R → ∃ y : Fin d → FractionRing (R ⧸ q), AlgebraicIndependent o y)
    (q : Ideal (FractionRing o ⊗[o] R)) (hq : q ∈ minimalPrimes (FractionRing o ⊗[o] R)) :
    (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  have hqp : q.IsPrime := hq.1.1
  let f : R →ₐ[o] FractionRing o ⊗[o] R := Algebra.TensorProduct.includeRight
  have hmin : q.comap f ∈ minimalPrimes R := by
    letI : Algebra R (FractionRing o ⊗[o] R) := Algebra.TensorProduct.rightAlgebra
    have h1 := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid R (nonZeroDivisors o))
      (FractionRing o ⊗[o] R) ⊥
    rw [Ideal.map_bot] at h1
    have h2 : q ∈ (⊥ : Ideal (FractionRing o ⊗[o] R)).minimalPrimes := hq
    rw [h1] at h2
    exact h2
  obtain ⟨y, hy⟩ := h (q.comap f) hmin
  let B := (FractionRing o ⊗[o] R) ⧸ q
  let f' : (R ⧸ q.comap f) →ₐ[o] FractionRing B :=
    (IsScalarTower.toAlgHom o B (FractionRing B)).comp (Ideal.quotientMapₐ q f le_rfl)
  have hf' : Function.Injective f' :=
    (IsFractionRing.injective B (FractionRing B)).comp (Ideal.quotientMap_injective' (f := f.toRingHom) (H := le_rfl) le_rfl)
  let j : FractionRing (R ⧸ q.comap f) →ₐ[o] FractionRing B := IsFractionRing.liftAlgHom hf'
  have h1 : AlgebraicIndependent o (j ∘ y) := hy.map' j.toRingHom.injective
  have : Algebra.IsAlgebraic o (FractionRing o) := IsLocalization.isAlgebraic _ (nonZeroDivisors o)
  have h2 := (h1.extendScalars (FractionRing o)).cardinalMk_le_trdeg
  have : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (FractionRing o) B
  have : FaithfulSMul (FractionRing o) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap (FractionRing o) B).injective
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top (FractionRing o) B (FractionRing B), hs2] at h2
  have h3 : d ≤ s := by simpa using h2
  rw [hs1]
  exact_mod_cast h3

theorem le_ringKrullDim_genericFibre : Out.Laws → Out.Laws2 → ∀ (g n N' : ℕ) (J : Type) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (w w' : J) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d : ℕ) (F : WFam n em C Mat κ), 3 ≤ N' → Odd N' → ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ F.U.toScheme), IsOpenImmersion x → x ≫ F.U.ι ≫ F.Y.s = spMap (algebraMap o R) → ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), (d : WithBot ℕ∞) ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q) := by
  intro h1 h2 g n N' J Mat κ w w' o _ b em C d F hN _ hb hC R _ _ x hox hx
  have : IsDedekindDomain o := hb.1
  have hx' : (x ≫ F.U.ι) ≫ F.Y.s = spMap (algebraMap o R) := by rw [Category.assoc, hx]
  have : Algebra.FiniteType o R := by
    obtain ⟨N, i, hi, -, hs⟩ := F.Y.qproj
    have := isProper_str o N
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := by
      rw [← hx', ← hs]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
    exact RingHom.finiteType_algebraMap.mp h
  refine le_ringKrullDim_of_independent fun q _ hq => ?_
  let y : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have hy : y.comp (algebraMap o R) = algebraMap o _ := by
    rw [IsScalarTower.algebraMap_eq o (R ⧸ q) (FractionRing (R ⧸ q))]; rfl
  obtain ⟨v, hv⟩ := exists_secCoord_field F.Y.isLB F.Y.th (spMap y ≫ x ≫ F.U.ι)
  have hK := F.Y.loc _ (y.comp (algebraMap o R)) _ _ (by rw [Category.assoc, hx', sp_comp]) hv
  obtain ⟨c, hc⟩ := hK.2 ⊥ Ideal.isPrime_bot 0
  obtain ⟨P, a₀, a, hP, hI, hle, -, hind⟩ := GlobalTheory.T.theta_ideal_prime_avoiding_variable h1 h2 g N' J Mat κ w w' o b em C d hb hC
    (RingHom.ker (MvPolynomial.eval₂Hom (y.comp (algebraMap o R)) v)) _ (by omega) (RingHom.ker_isPrime _)
    (fun G hG => hK.1 G hG) (by rw [RingHom.mem_ker, MvPolynomial.eval₂Hom_X']; simpa only [Ideal.mem_bot] using hc)
  obtain ⟨K, _, j, u, hker⟩ := exists_extension F.Y _ (x ≫ F.U.ι) hx' q hq y rfl v hv P hP hI hle
  refine ⟨fun i => v (a i) / v a₀, algebraicIndependent_iff.2 fun G hG => hind K _ _ hker G ?_⟩
  have := congrArg j hG
  rw [map_zero, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, ← hy] at this
  convert this using 2
  ext i
  simp [mul_div_mul_left]

end GlobalTheory.ZM.GenericDim
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l) (a : Xo.X ⟶ MM) (ν₀ : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l ≃+* KA l), 1 ≤ D.p + D.q → l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → Surjective (pullback.lift a _ h) → (∀ x, (Xo.univ.etaA x).left ≫ ν₀.φ = a ≫ (lev x).left) → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∃ (ρ : MM ≅ MM) (_ : SABMap tM tM ρ.hom) (σ₀ : RZ H n N ≃+* RZ H n N), a ≫ ρ.hom = r.hom ≫ a ∧ ρ.hom ≫ sM = sM ≫ spMap σ₀.toRingHom ∧ σ₀ (RZ.rt H n N) = RZ.rt H n N := by
  first | exact @GlobalTheory.famCore_exists_aut | exact GlobalTheory.famCore_exists_aut | (intros; apply GlobalTheory.famCore_exists_aut <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.moduli_finite_surjective_over_generic_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l), l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → N.Coprime l.M → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → ∃ (a : Xo.X ⟶ MM) (ν : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β), (∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left) ∧ IsFinite (pullback.lift a _ h) ∧ Surjective (pullback.lift a _ h) := by
  first | exact @GlobalTheory.moduli_finite_surjective_over_family | exact GlobalTheory.moduli_finite_surjective_over_family | (intros; apply GlobalTheory.moduli_finite_surjective_over_family <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → GeometricallyConnected (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.ConnOpen.geometricallyConnected_near | exact GlobalTheory.ConnOpen.geometricallyConnected_near | (intros; apply GlobalTheory.ConnOpen.geometricallyConnected_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.relAmple_formBundle_power_of_posDef : Out.GlobalFnsSt → ∀ (h k n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h k ζ s) (G : Over S) [GrpObj G] (pr : Fin n → (G ⟶ c.A)) (W : Matrix (Fin n) (Fin n) ℤ), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin n → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → Out.RelAmple c.A c.diag → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → Out.RelAmple G (LB.LinComb c.P (K := Fin n × Fin n) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef | exact GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef | (intros; apply GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.raised_model_finite_cover_ample_frames : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N k : ℕ) (T : Top Xo n N), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model (Xo l) c β), n.Prime → Odd n → (∃ e, N = n ^ e) → IsUnit (n : O) → l₀.Dvd l → IsDedFrac β → Raises B Y → Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L ((n ^ k) ^ 2)) → GlobalTheory.LN.Amp Y := by
  first | exact @GlobalTheory.RaisedAmple.amp_of_raises | exact GlobalTheory.RaisedAmple.amp_of_raises | (intros; apply GlobalTheory.RaisedAmple.amp_of_raises <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_reduced_of_dense :
    Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B] (M : LB B.left), IsAbelianScheme B → M.IsLB → Out.RelAmple B M → ∀ (S X : Scheme.{0}) [IsReduced S] (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S) (N : LB X), IsPullback π f B.hom t → N.IsLB → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (Y : Scheme.{0}) (ρ : Y ⟶ X) (h : Y ⟶ Sp K), p ∈ Set.range x ∧ IsPullback ρ h f x ∧ ∃ c : (N.pull ρ).Gen, c.IsGen} → ∀ σ : S ⟶ X, σ ≫ f = 𝟙 S → (∃ c : (N.pull σ).Gen, c.IsGen) → ∃ c : N.Gen, c.IsGen := by
  intro hG S₀ B _ M hB hM hA S X _ t π f N hp hN hd σ hσ hc
  exact GlobalTheory.exists_gen_of_local_of_section X S f σ N hN hσ
    (GlobalTheory.BaseChangeFns.app_surjective hG S₀ B hB S X t π f hp)
    (GlobalTheory.SeesawLocal.triv_locally_of_dense S₀ B M hB hM hA S X t π f N hp hN hd) hc

end GlobalTheory
end
