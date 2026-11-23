module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle001
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

set_option linter.overlappingInstances false

open IsLocalRing Matrix UpperTheory.V UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

private theorem tw_map (f : A →ₐ[O] A') (ρ : NRep F n A) :
    (W.GDet.ofRep (K.tw ρ)).map (f : A →+* A') = W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))) := by
  rw [(CA.d_gmap (W.GDet.ofRep (K.tw ρ))).2.2.2]
  congr 1
  ext g i j
  simp [TwLink.tw, TwLink.κA]

private theorem twψ_map (f : A →ₐ[O] A') (ρ : NRep F n A) (v : G.Vl) (i : Fin n) :
    W.pushCh (f : A →+* A') (K.twψ ρ v i) = K.twψ (ρ.map (f : A →+* A')) v i := by
  ext g
  simp [TwLink.twψ, TwLink.κA]

private theorem maps_comp (B : W.UniversalOrdinaryDeterminantRing r) (φ : B.B →ₐ[O] A) (f : A →ₐ[O] A') (ρ : NRep F n A)
    (h : B.u.Maps (φ : B.B →+* A) (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ)) :
    B.u.Maps ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))))
      (K.twψ (ρ.map (f : A →+* A'))) := by
  refine ⟨?_, fun v i => ?_⟩
  · rw [← tw_map, ← h.1, (CA.d_gmap B.u.D).2.1]
    rfl
  · rw [← twψ_map, ← h.2]
    rfl

private theorem maps_of_inj (B : W.UniversalOrdinaryDeterminantRing r) (φ : B.B →ₐ[O] A) (f : A →ₐ[O] A') (hf : Function.Injective f)
    (ρ : NRep F n A)
    (h : B.u.Maps ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') (W.GDet.ofRep (K.tw (ρ.map (f : A →+* A'))))
      (K.twψ (ρ.map (f : A →+* A')))) :
    B.u.Maps (φ : B.B →+* A) (W.GDet.ofRep (K.tw ρ)) (K.twψ ρ) := by
  have hc : ((f.comp φ : B.B →ₐ[O] A') : B.B →+* A') = (f : A →+* A').comp (φ : B.B →+* A) := rfl
  have hinj : Function.Injective (f : A →+* A') := hf
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun v i => ?_⟩
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (X := Unit) (fun _ => A') (fun _ => (f : A →+* A'))
      (fun a ha => hinj (by rw [ha (), map_zero]))).1 _ _ (fun _ => ?_)
    rw [(UpperTheory.V.CA.d_gmap B.u.D).2.1, ← hc, h1, tw_map]
  · ext g
    have := congrArg (fun χ => ((χ g : A'ˣ) : A')) (h2 v i)
    simp only [hc, ← twψ_map] at this
    exact hinj this

end

theorem UpperTheory.V.Pr.goodPtOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.GoodPtOf := by
  intro l _ O _ _ _ _ _ F n T Φ hΦ J hJ A _ _ _ ρ hρ K' _ j hj hirr
  have hcl : CA.IsCL O A :=
    { noeth := PrincipalIdealRing.isNoetherianRing
      complete := inferInstance
      isLocalHom := inferInstance
      res_fin := Module.Finite.of_finite }
  obtain ⟨ξ, hξ, -⟩ := point_loc T.ok T.n23 T.S A hcl (ResidueField.map (algebraMap O A)) (fun _ => rfl) ρ
    hρ.cont hρ.bar
  have hTI : T.S.u.TI (RingHom.ker (j.comp (ξ : T.S.A →+* A))) := by
    refine (types T.ok T.n23 T.S K' (j.comp (ξ : T.S.A →+* A))).1.1 ?_
    rw [← NRep.map_map, hξ]
    exact hirr
  have hle := hJ _ (RingHom.ker_isPrime _) hTI
  refine ⟨ξ.comp (T.S.inc.comp Φ), fun x hx => ?_, ?_⟩
  · have h1 := hle (Ideal.mem_map_of_mem _ hx)
    exact hj (Eq.trans h1 (map_zero j).symm)
  · have hu : T.S.u.map (T.S.A.val : T.S.A →+* T.S.R) = T.S.ρ := by
      refine NRep.ext ?_ ?_
      · ext g i j
        rfl
      · funext v i
        ext g
        rfl
    have hc : T.S.A.val.comp (T.S.inc.comp Φ) = T.S.B.val.comp Φ := AlgHom.ext fun _ => rfl
    have h2 := maps_comp T.K T.B (T.S.inc.comp Φ) ξ T.S.u
      (maps_of_inj T.K T.B (T.S.inc.comp Φ) T.S.A.val Subtype.val_injective T.S.u (by rw [hu, hc]; exact hΦ))
    rwa [hξ] at h2
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

section
open Polynomial UpperTheory.V.W

private theorem chi_ofRep' {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  show Matrix.det (GDet.repAlg ρ A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)) = _
  rw [map_sub]
  congr 2
  simp [GDet.repAlg, MonoidAlgebra.lift_single, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]

private theorem prod_diagonal {n : ℕ} {A : Type} [CommRing A] (L : List (Fin n → A)) :
    (L.map Matrix.diagonal).prod = Matrix.diagonal L.prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons, Matrix.diagonal_mul_diagonal]
    rfl

private theorem rep_oEl {l : ℕ} [Fact l.Prime] {G : GFrame l} {k : Type} [CommRing k] {n : ℕ}
    (χ : Fin n → G.G₀ →* kˣ) (v : G.Vl) (ψ : Fin n → G.Gv v →* kˣ) (h : ∀ i g, ψ i g = χ i (G.φ v g))
    (g : Fin n → G.Gv v) :
    GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C (G.oEl v ψ g)) = 0 := by
  have hf : ∀ i, GDet.repAlg (diagRep χ) k[X] (MonoidAlgebra.mapRingHom _ C
      (MonoidAlgebra.single (G.φ v (g i)) 1 - MonoidAlgebra.single 1 ((ψ i (g i) : kˣ) : k))) =
      Matrix.diagonal (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)) := by
    intro i
    simp [GDet.repAlg, MonoidAlgebra.lift_single, diagRep, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_sub]
  unfold GFrame.oEl
  rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  simp only [Function.comp_def, hf]
  have key : (List.ofFn fun i => Matrix.diagonal
      (fun j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k))) =
      (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).map
        Matrix.diagonal := by
    rw [List.map_ofFn]
    rfl
  rw [key, prod_diagonal]
  have hz : (List.ofFn fun i j => C ((χ j (G.φ v (g i)) : kˣ) : k) - C ((ψ i (g i) : kˣ) : k)).prod
      = 0 := by
    funext j
    rw [List.prod_ofFn, Finset.prod_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [h]
  rw [hz]
  exact Matrix.diagonal_zero

end

theorem UpperTheory.residual_ok_of_local_chars_restrict :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l]
      {G : W.GFrame l} {n : ℕ} (r : W.Resid G O n), 1 ≤ n →
      (∀ v i g, r.psib v i g = r.chib i (G.φ v g)) → r.Ok := by
  intro l _ O _ _ _ _ G n r hn hps
  refine ⟨fun v g h => ?_, fun v i g => ?_⟩
  · simp only [W.Resid.Dbar, W.GDet.tr, W.GDet.lam]
    rw [chi_ofRep', map_mul, map_mul, rep_oEl r.chib v (r.psib v) (hps v) g, mul_zero, sub_zero,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  · rw [(W.residualDatum_inertia_characters_trivial l G O n r v i g).1, (W.residualDatum_inertia_characters_trivial l G O n r v i g).2]
end
