module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.PencilDisc

theorem resultant_derivative_ne_zero : ∀ (σ F : Type) [Fintype σ] [Field F] [CharZero F] (p : Polynomial (MvPolynomial σ F)) (δ : ℕ), 1 ≤ δ → p.natDegree = δ → Irreducible p → Polynomial.resultant p (Polynomial.derivative p) δ (δ - 1) ≠ 0 := by
  intro σ F _ _ _ p δ hδ hp hirr
  let K := FractionRing (MvPolynomial σ F)
  have hinj : Function.Injective (algebraMap (MvPolynomial σ F) K) := IsFractionRing.injective _ _
  haveI : CharZero K := charZero_of_injective_algebraMap hinj
  have hprim : p.IsPrimitive := hirr.isPrimitive (by omega)
  have h1 : Irreducible (p.map (algebraMap _ K)) := hprim.irreducible_iff_irreducible_map_fraction_map.1 hirr
  have h2 := Polynomial.resultant_ne_zero _ _ h1.separable
  rw [Polynomial.natDegree_derivative, Polynomial.natDegree_map_eq_of_injective hinj, hp, Polynomial.derivative_map,
    Polynomial.resultant_map_map] at h2
  intro h
  exact h2 (by rw [h, map_zero])

theorem exists_specialise_ne_zero : ∀ (F S T : Type) [Field F] [Infinite F] (R : MvPolynomial (S ⊕ T) F), R ≠ 0 → ∃ v : T → F, MvPolynomial.aeval (Sum.elim (fun i => (MvPolynomial.X i : MvPolynomial S F)) fun k => MvPolynomial.C (v k)) R ≠ 0 := by
  intro F S T _ _ R hR
  have h1 : sumAlgEquiv F S T R ≠ 0 := (map_ne_zero_iff _ (sumAlgEquiv F S T).injective).2 hR
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.1 h1
  obtain ⟨v, hv⟩ : ∃ v : T → F, eval v (AddMonoidAlgebra.coeff (sumAlgEquiv F S T R) m) ≠ 0 := by
    by_contra! H
    exact hm (MvPolynomial.funext fun x => by simpa using H x)
  refine ⟨v, fun h => hv ?_⟩
  have key : ∀ P : MvPolynomial (S ⊕ T) F,
      aeval (Sum.elim (fun i => (X i : MvPolynomial S F)) fun k => C (v k)) P = MvPolynomial.map (eval v) (sumAlgEquiv F S T P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      cases i <;> simp
  rw [← coeff_map, ← key, h]
  simp

theorem irreducible_of_map {F L : Type} [Field F] [Field L] [Algebra F L] {σ : Type} (f : MvPolynomial σ F)
    (h : Irreducible (MvPolynomial.map (algebraMap F L) f)) : Irreducible f := by
  have hinj := (algebraMap F L).injective
  haveI : IsLocalHom (MvPolynomial.map (σ := σ) (algebraMap F L)) := ⟨fun g hg => by
    obtain ⟨c, hc, e⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.1 hg
    have hc0 : algebraMap F L (AddMonoidAlgebra.coeff g 0) = c := by
      rw [← coeff_map, e, coeff_zero_C]
    refine MvPolynomial.isUnit_iff_eq_C_of_isReduced.2 ⟨AddMonoidAlgebra.coeff g 0, ?_, ?_⟩
    · refine isUnit_iff_ne_zero.2 fun h0 => hc.ne_zero ?_
      rw [← hc0, h0, map_zero]
    · apply MvPolynomial.map_injective _ hinj
      rw [e, map_C, hc0]⟩
  exact Irreducible.of_map h

theorem exists_poly_noSquare : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F), 1 ≤ δ → IsMultiHomogeneous (fun _ => δ) f → Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) → ∃ Q : MvPolynomial (Fin D × Fin N) F, Q ≠ 0 ∧ Q.totalDegree ≤ 2 * D * δ ^ 2 ∧ ∀ (K : Type) [Field K] [Algebra F K] (s : Fin D → Fin N → K), aeval (fun p : Fin D × Fin N => s p.1 p.2) Q ≠ 0 → NoSquare (spec s f) := by
  intro F _ _ D N δ f hδ hf hirr
  have hF : Irreducible f := irreducible_of_map f hirr
  let u : Fin D → Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun i j => X (Sum.inl (i, j))
  let a : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inl j))
  let b : Fin N → MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F := fun j => X (Sum.inr (Sum.inr j))
  have hc := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F _ D N δ f hf u a b
  let g : Fin (D + 1) × Fin N → (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N) := fun p =>
    Fin.lastCases (motive := fun _ => (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) (Sum.inr (Sum.inr p.2)) (fun i => Sum.inl (i, p.2)) p.1
  have hg : Function.Injective g := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    induction i using Fin.lastCases <;> induction i' using Fin.lastCases <;> simp_all [g]
  have hjoin : join u b = fun p => X (g p) := by
    funext ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, g, u, b]
  have hlead : (line u a b f).coeff δ ≠ 0 := by
    rw [hc.2, hjoin, show (aeval fun p => (X (g p) : MvPolynomial _ F)) f = rename g f from congrArg (fun φ : MvPolynomial _ F →ₐ[F] MvPolynomial _ F => φ f) (MvPolynomial.algHom_ext fun p => by simp)]
    exact (rename_injective g hg).ne_iff' (map_zero _) |>.mpr hF.ne_zero
  have hnat : (line u a b f).natDegree = δ := le_antisymm hc.1 (Polynomial.le_natDegree_of_ne_zero hlead)
  have hR : disc δ u a b f ≠ 0 := resultant_derivative_ne_zero _ F (line u a b f) δ hδ hnat (GlobalTheory.T.irreducible_pencilLinePolynomial_generic_line F D N f hF)
  obtain ⟨v, hv⟩ := exists_specialise_ne_zero F (Fin D × Fin N) (Fin N ⊕ Fin N) _ hR
  refine ⟨disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F)) (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f,
    ?_, GlobalTheory.T.totalDegree_pencilLineDiscriminant_le F D N δ f hf _ _, ?_⟩
  · have e := map_disc (aeval (Sum.elim (fun i => (X i : MvPolynomial (Fin D × Fin N) F)) fun k => C (v k))) δ u a b f
    rw [e] at hv
    simpa [u, a, b] using hv
  · intro K _ _ s hs
    have e := map_disc (aeval (fun p : Fin D × Fin N => s p.1 p.2)) δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (v (Sum.inl j))) (fun j => C (v (Sum.inr j))) f
    rw [e] at hs
    simp only [aeval_X, aeval_C] at hs
    have hc' := GlobalTheory.T.pencilLinePolynomial_natDegree_le_and_coeff F K D N δ f hf s (fun j => algebraMap F K (v (Sum.inl j))) (fun j => algebraMap F K (v (Sum.inr j)))
    exact GlobalTheory.T.not_square_linear_factor_of_pencilLineDiscriminant_ne_zero F K D N δ f s _ _ hδ hc'.1 hc'.2 hs

end GlobalTheory.PencilDisc
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_dat_chi_eq (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (N : ℕ) (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ (p ^ N) : Pt A D) = 1 → GlobalTheory.PtExt.chi (p ^ N) d.g D x = b D x := by
  have : IsCommMonObj A := hA.comm
  have hn : ((p ^ N : ℕ) : R) = 0 := by
    simpa only [Nat.cast_pow] using hN
  have hR : GlobalTheory.PtExt.HasRoots A (p ^ N) := fun D _ _ x ↦
    GlobalTheory.PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N) D x
  obtain ⟨u, g, hu, hg, hchi⟩ := GlobalTheory.T.exists_pushout_torsor_nTorsion_character R A (p ^ N) hn hR b hb
  obtain ⟨f, hf⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R A hs u hu
  obtain ⟨g', hg', hchi'⟩ := GlobalTheory.CobChi.exists_isAdd_chi_eq R A (p ^ N) hn u (fv f) g hg hf
  let c : primDR A := ⟨H1.mk _ f, by rw [show primDR A = ⊤ from hP]; exact Submodule.mem_top⟩
  obtain ⟨d, -, hd⟩ := GlobalTheory.PtExt.exists_dat_of_isAdd R A p G t c f rfl g' hg'
  refine ⟨c, d, fun D _ _ x hx ↦ ?_⟩
  rw [hd, hchi' D x hx, hchi D x hx]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

private theorem top_le_comp_preimage {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

private theorem top_le_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  rwa [Scheme.Hom.comp_preimage] at h

private theorem top_le_preimage_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens} (hA : ⊤ ≤ f ⁻¹ᵁ A)
    (hB : ⊤ ≤ f ⁻¹ᵁ B) : ⊤ ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun y _ => ⟨hA trivial, hB trivial⟩

private theorem evAt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) : evAt ξ h = evAt ξ' h' := by
  subst e; rfl

private def resO {k K E : Type} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E]
    {ρ : Place k E → Place k K} (hρ : IsRes ρ) (p : Place k E) : (ρ p).O →+* p.O :=
  ((algebraMap K E).comp (ρ p).O.subtype).codRestrict p.O fun y =>
    (Valuation.mem_valuationSubring_iff _ _).2 ((hρ p y).2 ((Valuation.mem_valuationSubring_iff _ _).1 y.2))

private def constO {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) : k →+* p.O :=
  (algebraMap k E).codRestrict p.O fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (p.2.2 c hc).le

theorem genPath_scaling : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x _ G _ hG W r i V₀ s ρ hρ p g hg w u hu hpu ξ hξ hξt
  have hsm : Smooth G.hom := hG.smooth
  have hqs : QuasiSeparated G.hom := by haveI := hG.separated; infer_instance
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨b₀, V, t, Vf, h₀, h₁, hxf, M, hb₀, hb₀V, -, hst, rfl⟩ := hg
  set xE := spMap (algebraMap K E) ≫ x with hxE
  let α := resO hρ p
  let φ : p.O →+* E := p.O.subtype
  let b : Sp p.O ⟶ C := spMap α ≫ b₀
  have hbx : spMap φ ≫ b = xE := by
    rw [hxE, ← hb₀]
    simp only [b, ← Category.assoc, spMap, ← Spec.map_comp]
    rfl
  letI : Algebra ℚ p.O := ((constO p).comp (algebraMap ℚ k)).toAlgebra
  have hbV : ⊤ ≤ b ⁻¹ᵁ V := top_le_comp_preimage _ _ hb₀V
  let y : Fin r → E := ((M.map (evAt x hxf)).map (algebraMap K E)).mulVec w
  let eE : Fin r → E := fun j => u⁻¹ * y j
  have heO : ∀ j, eE j ∈ p.O := by
    intro j
    rw [Valuation.mem_valuationSubring_iff]
    have hle : p.1 (y j) ≤ p.1 u := by
      rw [hpu, nrm]; exact Finset.le_sup (f := fun i => p.1 (y i)) (Finset.mem_univ j)
    have hu0 : p.1 u ≠ 0 := (Valuation.ne_zero_iff _).2 hu
    calc p.1 (eE j) = (p.1 u)⁻¹ * p.1 (y j) := by simp only [eE, map_mul, map_inv₀]
      _ ≤ (p.1 u)⁻¹ * p.1 u := by gcongr
      _ = 1 := inv_mul_cancel₀ hu0
  let e : Fin r → p.O := fun j => ⟨eE j, heO j⟩
  obtain ⟨ζ, hζ, hζt⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G p.O hsm hqs b r V (fun j => i.app V (t j)) e hbV
  obtain ⟨U₀, hU₀a, hζU₀, -⟩ := Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens
    (Opens.mem_top (ζ (IsLocalRing.closedPoint (PowerSeries p.O))))
  have hζU : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left ζ U₀).2 hζU₀
  have hξ'U : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := top_le_comp_preimage _ _ hζU
  have hξ'path : IsPath G 2 xE (spMap (sc p u) ≫ ζ) := by
    have := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).1
    rw [map_ofNat, hbx] at this
    exact this

  have hxEf : ⊤ ≤ xE ⁻¹ᵁ Vf := top_le_comp_preimage _ _ hxf
  have hxE0 : ⊤ ≤ xE ⁻¹ᵁ V₀ := hxEf.trans (Scheme.Hom.preimage_mono xE h₀)
  have hxEu : ⊤ ≤ xE ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hξ'path.zero]; exact top_le_comp_preimage _ _ hξ'U
  have hbu : ⊤ ≤ b ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hζ.zero]; exact top_le_comp_preimage _ _ hζU
  have hxs : ⊤ ≤ xE ⁻¹ᵁ (Vf ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hxEf hxEu
  have hb'' : ⊤ ≤ b ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hbV hbu
  have hxE'' : ⊤ ≤ xE ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := by rw [← hbx]; exact top_le_comp_preimage _ _ hb''
  have hsub : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V ⊓ unitSec G ⁻¹ᵁ U₀ := inf_le_inf_right _ h₁
  have key : ∀ f : Γ(G.left, U₀), PowerSeries.coeff 1 (evAt (spMap (sc p u) ≫ ζ) hξ'U f) =
      ∑ j, w j * evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) := by
    intro f
    have h1 := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).2 r V (fun j => i.app V (t j)) e hbV U₀ hζU hζt hξ'U
      (V ⊓ unitSec G ⁻¹ᵁ U₀) inf_le_left inf_le_right hb'' f
    have hD : ∀ τ : Γ(Lie G, V), φ (evAt b hb'' (dualApp τ inf_le_left (dUnit G inf_le_right f))) =
        evAt xE hxs (dualApp τ (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro τ
      rw [← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 p.O E C φ b _ hb'' (top_le_comp_preimage _ _ hb''), evAt_congr hbx _ hxE'',
        ← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE _ _ hsub hxE'' hxs]
      congr 1
      have := dualApp_resM τ (inf_le_left : V ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V) hsub (dUnit G inf_le_right f)
      rw [resM_dUnit] at this
      exact this.symm
    have hR : ∀ j, evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) =
        ∑ l, algebraMap K E (evAt x hxf (M l j)) * evAt xE hxs (dualApp (i.app V (t l))
          (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro j
      have e1 : dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) =
          dualApp (resM _ h₀ (i.app V₀ (s j))) (inf_le_left : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ Vf) :=
        (dualApp_res _ _ _).symm
      have e2 : resM _ h₀ (i.app V₀ (s j)) = ∑ l, M l j • resM _ h₁ (i.app V (t l)) := by

        rw [← GlobalTheory.Twist.app_resM, hst, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]

      rw [e1, e2, dualApp_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, dualApp_res]
      congr 1
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE Vf _ inf_le_left hxEf hxs (M l j)).trans
        (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x Vf hxf hxEf (M l j))
    have he' : ∀ l, u * φ (e l) = ∑ j, algebraMap K E (evAt x hxf (M l j)) * w j := by
      intro l
      show u * (u⁻¹ * y l) = _
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.one_mul]
      simp [y, Matrix.mulVec, dotProduct]
    refine Eq.trans h1 ?_
    simp only [hD, hR, he', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have htan' : HasTan G xE (spMap (sc p u) ≫ ζ) (fun j => i.app V₀ (s j)) w :=
    GlobalTheory.T.hasTangent_of_single_affineChart C G E 2 xE _ hξ'path r V₀ _ w U₀ hU₀a hξ'U _ (inf_le_left.trans h₀) inf_le_right hxs key
  have hunit : ∀ j, 2 ≤ j → IsUnit ((2 : E) ^ j - 2) := by
    intro j hj
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have hc : ((2 ^ j - 2 : ℕ) : E) = 0 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ j)]; push_cast; exact h0
    rw [Nat.cast_eq_zero] at hc
    omega
  have heq : ξ = spMap (sc p u) ≫ ζ := by
    refine GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees C G E hqs 2 2 (by norm_num) hunit xE ξ _ hξ hξ'path ?_
    intro U h h' f j hj0 hj2
    obtain rfl : j = 1 := by omega
    have hb3 : ⊤ ≤ xE ⁻¹ᵁ (V₀ ⊓ unitSec G ⁻¹ᵁ U) := by
      refine top_le_preimage_inf _ hxE0 ?_
      apply top_le_of_comp
      rw [← hξ.zero]; exact top_le_comp_preimage _ _ h
    rw [hξt U h _ inf_le_left inf_le_right hb3 f, htan' U h' _ inf_le_left inf_le_right hb3 f]
  exact ⟨b, ζ, hbx, hζ, heq⟩

end GlobalTheory.Nef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem comp_grpMul {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (x : T' ⟶ T) (f g : T ⟶ G) :
    x ≫ (f * g) = (x ≫ f) * (x ≫ g) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G := by
  have h1 : (η[G] : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, Subsingleton.elim (toUnit (𝟙_ (Over S))) (𝟙 _), Category.id_comp]
  have : (η[G] : 𝟙_ (Over S) ⟶ G) ≫ (𝟙 G * 𝟙 G) = η[G] := by
    rw [comp_grpMul, Category.comp_id, h1, _root_.one_mul]
  exact congrArg (·.left) this

theorem triv_isPath {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (c : R) (b : Sp R ⟶ S) :
    IsPath G c b (triv G b) := by
  refine { base := triv_over G b, zero := ?_, scale := ?_ }
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.constantCoeff (R := R))) = 𝟙 _ := by
      ext x; simp
    rw [this, Spec.map_id, Category.id_comp]
  · rw [triv, ← Category.assoc, spMap, spMap, ← Spec.map_comp]
    have : (CommRingCat.ofHom (PowerSeries.C (R := R)) ≫ CommRingCat.ofHom (PowerSeries.rescale c)) = CommRingCat.ofHom (PowerSeries.C (R := R)) := by
      ext x n; simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
      split_ifs with h <;> simp [h]
    rw [this, Category.assoc, Category.assoc, unitSec_comp_sqr]

theorem eq_unitSec_of_sqr_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (z : Sp R ⟶ G.left)
    (hz : z ≫ sqr G = z) : z = (z ≫ G.hom) ≫ unitSec G := by
  let z' : Over.mk (z ≫ G.hom) ⟶ G := Over.homMk z rfl
  have h : z' * z' = z' := by
    have e := comp_grpMul z' (𝟙 G) (𝟙 G)
    rw [Category.comp_id] at e
    rw [← e]
    ext
    exact hz
  have h1 : z' = 1 := by simpa using h
  have h2 := congrArg (·.left) h1
  rw [Hom.one_def] at h2
  refine h2.trans ?_
  rw [Over.comp_left]
  congr 1

end GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem triv_unique : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], (∀ (c : R) (b : Sp R ⟶ S), IsPath G c b (triv G b)) ∧ (∀ (z : Sp R ⟶ G.left), z ≫ sqr G = z → z = (z ≫ G.hom) ≫ unitSec G) ∧ (∀ [IsLocalRing R], QuasiSeparated G.hom → ∀ (c : R), (∀ j, 1 ≤ j → IsUnit (c ^ j - 2)) → ∀ (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → ξ = triv G b) := by
  intro S G _ R _
  refine ⟨fun c b => triv_isPath G c b, fun z hz => eq_unitSec_of_sqr_eq G z hz, ?_⟩
  intro _ hq c hc b ξ hξ
  exact GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees S G R hq c 1 one_pos hc b ξ (triv G b) hξ (triv_isPath G c b)
    (fun _ _ _ _ j hj hj' => absurd hj' (by omega))

end GlobalTheory.Nef
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.torusExtension_characterValue_constantTerm_one : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → ∀ (χ : D.X),
    (vE (gm.s χ) (𝟙 _) ν.J).fst = 1 := by
  first | exact @GlobalTheory.MBLow.Cl.fst_vE_eq_one | exact GlobalTheory.MBLow.Cl.fst_vE_eq_one | (intros; apply GlobalTheory.MBLow.Cl.fst_vE_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.torusExtension_dualCharValues_mul_cube : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    (ν : NumOf D ℂ N) (gm : GtPt D (TE R ℂ)) (χ χ' : D.X),
    vE (gm.s (χ + χ')) (𝟙 _) ν.J *
        vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      vE (gm.s χ) (𝟙 _) ν.J * vE (gm.s χ') (𝟙 _) ν.J := by
  first | exact @GlobalTheory.DualMult.mult_vE | exact GlobalTheory.DualMult.mult_vE | (intros; apply GlobalTheory.DualMult.mult_vE <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.arith_small_sections_encard_mul_le_finite_level : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ), (P.Bl N m 1).Finite → (P.Bl N m 1).encard * (P.Bl 0 (b * N) 1).encard ≤ {f | f ∈ P.H N 0 ∧ f * s ^ m ∈ P.Bl N m 2}.encard * (P.Bl 0 (b * N + m) 2).encard := by
  first | exact @GlobalTheory.VolBr.encard_mul_le_at_level | exact GlobalTheory.VolBr.encard_mul_le_at_level | (intros; apply GlobalTheory.VolBr.encard_mul_le_at_level <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_hermitianRepresentative_integerCombination : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b : ℤ), ∃ M : HermLB p, P.Rep a b M := by
  first | exact @GlobalTheory.VolBr.Pair.exists_rep | exact GlobalTheory.VolBr.Pair.exists_rep | (intros; apply GlobalTheory.VolBr.Pair.exists_rep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.arith_global_maximum_principle_off_divisor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ (N : ℕ) (f : X.functionField) (R : ℝ), f ∈ P.H N 0 → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ρ ≤ P.nu 0 1 σ y s → P.nu N 0 σ y f ≤ R) → f ∈ P.Bl N 0 (Real.exp (δ * N) * R) := by
  first | exact @GlobalTheory.VolBr.max_principle_global | exact GlobalTheory.VolBr.max_principle_global | (intros; apply GlobalTheory.VolBr.max_principle_global <;> assumption)
end
