module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle963
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle935
public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle968
public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle967
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

theorem _root_.GlobalTheory.T.artinian_lift_axes_wedge : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  first | exact @GlobalTheory.AbCoh.SmallStepSurj.surj_of_smallExt | exact GlobalTheory.AbCoh.SmallStepSurj.surj_of_smallExt | (intros; apply GlobalTheory.AbCoh.SmallStepSurj.surj_of_smallExt <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_of_iso {k : Type} [CommRing k] {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k) (e : X' ≅ X)
    (he : e.hom ≫ s = s') (hW : WedgeO (OAff s)) : WedgeO (OAff s') := by
  have h1 : e.hom ≫ s = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, he]
  have h2 : e.inv ≫ s' = s ≫ spMap (RingHom.id k) := by
    rw [spMap_id, Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have hid : (𝟙 X) ≫ s = s ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have hid' : (𝟙 X') ≫ s' = s' ≫ spMap (RingHom.id k) := by rw [spMap_id, Category.comp_id, Category.id_comp]
  have P := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  have c1 := (P.1 k k X X' s s' (RingHom.id k) e.hom h1 k X s (RingHom.id k) e.inv h2 (RingHom.id k) (𝟙 X) hid
    (by simp) (fun _ ↦ rfl))
  have c2 := (P.1 k k X' X s' s (RingHom.id k) e.inv h2 k X' s' (RingHom.id k) e.hom h1 (RingHom.id k) (𝟙 X') hid'
    (by simp) (fun _ ↦ rfl))
  have i1 := P.2.2 k (Over.mk s)
  have i2 := P.2.2 k (Over.mk s')
  have hcup := (P.2.1 k k X X' s s' (RingHom.id k) e.hom h1).1

  let f1 : HO1 s →ₗ[k] HO1 s' := pullHO1 h1
  let g1 : HO1 s' →ₗ[k] HO1 s := pullHO1 h2
  let f2 : HO2 s →ₗ[k] HO2 s' := pullHO2 h1
  let g2 : HO2 s' →ₗ[k] HO2 s := pullHO2 h2
  have fg1 : ∀ a, f1 (g1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c2.1]; exact i2.1 a
  have gf1 : ∀ a, g1 (f1 a) = a := fun a ↦ by simp only [f1, g1]; rw [c1.1]; exact i1.1 a
  have fg2 : ∀ a, f2 (g2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c2.2.1]; exact i2.2.1 a
  have gf2 : ∀ a, g2 (f2 a) = a := fun a ↦ by simp only [f2, g2]; rw [c1.2.1]; exact i1.2.1 a
  let e2 : HO2 s ≃ₗ[k] HO2 s' := LinearEquiv.ofLinear f2 g2 (LinearMap.ext fg2) (LinearMap.ext gf2)
  let eΛ : ⋀[k]^2 (HO1 s') ≃ₗ[k] ⋀[k]^2 (HO1 s) :=
    LinearEquiv.ofLinear (exteriorPower.map 2 g1) (exteriorPower.map 2 f1)
      (by rw [← exteriorPower.map_comp, show g1 ∘ₗ f1 = LinearMap.id from LinearMap.ext gf1,
        exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show f1 ∘ₗ g1 = LinearMap.id from LinearMap.ext fg1,
        exteriorPower.map_id])
  obtain ⟨E, hE⟩ := hW
  refine ⟨(eΛ.trans E).trans e2, fun a b ↦ ?_⟩
  have hm : (⇑g1 ∘ ![a, b]) = ![g1 a, g1 b] := by
    ext i; fin_cases i <;> rfl
  change f2 (E (exteriorPower.map 2 g1 (exteriorPower.ιMulti k 2 ![a, b]))) = _
  rw [exteriorPower.map_apply_ιMulti, hm, hE]
  simp only [f2]
  rw [hcup]
  rw [show pullHO1 h1 (g1 a) = a from fg1 a, show pullHO1 h1 (g1 b) = b from fg1 b]

end GlobalTheory.AbCohWedgeLift

namespace GlobalTheory.AbCohWedgeLift

theorem wedgeO_fibre : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), WedgeO (OAff s₀) := by
  intro hF R _ A _ g hA hg k _ σ X₀ s₀ ψ w
  letI : Algebra R k := σ.toAlgebra
  obtain ⟨B, _, pr, -, hB, hBg, hsq, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R k A g hA hg
  have hsq' : IsPullback pr B.hom A.hom (spMap σ) := hsq
  have hW : WedgeO (OAff B.hom) := (hF k (Field.toIsField k) B g hB hBg).2.2
  let e : X₀ ≅ B.left := IsPullback.isoIsPullback _ _ w hsq'
  exact wedgeO_of_iso B.hom s₀ e (IsPullback.isoIsPullback_hom_snd _ _ w hsq') hW

end GlobalTheory.AbCohWedgeLift
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1 := by
  first | exact @GlobalTheory.FinGL.whDim_parInd_eq_one | exact GlobalTheory.FinGL.whDim_parInd_eq_one | (intros; apply GlobalTheory.FinGL.whDim_parInd_eq_one <;> assumption)
end

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem _root_.GlobalTheory.T.symmetricPositionCharMultiplicity_parabolicInduction : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ ρ k : ℕ, ρ + k + 1 ≤ r → nPos ψ (parInd b σ) ρ k = ∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam (Fintype.card F) (k - j) := by
  first | exact @GlobalTheory.FinGL.nPos_parInd | exact GlobalTheory.FinGL.nPos_parInd | (intros; apply GlobalTheory.FinGL.nPos_parInd <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem pow_smul_cancel {G H : PDivGroup p k} (a : ℕ) {X Y : G ⟶ H}
    (h : (p : ℤ_[p]) ^ a • X = (p : ℤ_[p]) ^ a • Y) : X = Y := by
  induction a generalizing X Y with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    rw [← sub_eq_zero, ← smul_sub]
    apply eq_zero_of_prime_smul_eq_zero
    rw [smul_smul, ← pow_succ', smul_sub, h, sub_self]

theorem finrank_A (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  simpa [Module.rankAtStalk_eq_finrank_of_free] using h

theorem isIsog_pow_smul_id (G : PDivGroup p k) (m : ℕ) : IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) :=
  ⟨m, 𝟙 G, Category.comp_id _, Category.id_comp _⟩

theorem hasLogDeg_pow_smul_id (G : PDivGroup p k) (m : ℕ) :
    HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height) := by
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨f, hf, hk⟩ := G.exists_res_le hn
  have e : Hom.app ((p : ℤ_[p]) ^ m • 𝟙 G) n = mulBy (R := k) (A := G.A n) (p ^ m) := by
    rw [← Nat.cast_pow, natCast_smul_id_app]
  rw [e]
  change Module.finrank k (G.A n ⧸ torsionIdeal (R := k) (A := G.A n) (p ^ m)) = _
  rw [← hk]
  exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq).trans
    (finrank_A G m)

theorem isIsog_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hg : IsIsog g) : IsIsog (f ≫ g) := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, g', h3, h4⟩ := hg
  refine ⟨a + b, g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ g' ≫ f' = f ≫ (g ≫ g') ≫ f' := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 G := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h1, smul_smul, ← pow_add,
          add_comm b a]
  · calc (g' ≫ f') ≫ f ≫ g = g' ≫ (f' ≫ f) ≫ g := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by
        rw [h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h4, smul_smul, ← pow_add]

theorem isIsog_of_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hfg : IsIsog (f ≫ g)) : IsIsog g := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, u, h3, h4⟩ := hfg
  refine ⟨a + b, (p : ℤ_[p]) ^ a • (u ≫ f), ?_, ?_⟩
  · calc g ≫ ((p : ℤ_[p]) ^ a • (u ≫ f)) = ((p : ℤ_[p]) ^ a • 𝟙 H) ≫ g ≫ u ≫ f := by
          rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
      _ = f' ≫ ((f ≫ g) ≫ u) ≫ f := by rw [← h2]; simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 H := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h2, smul_smul, ← pow_add,
          add_comm b a]
  · calc ((p : ℤ_[p]) ^ a • (u ≫ f)) ≫ g = (p : ℤ_[p]) ^ a • (u ≫ f ≫ g) := by
          rw [Linear.smul_comp, Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by rw [h4, smul_smul, ← pow_add]

variable [CharP k p]

theorem hasLogDeg_zero_iff_isIso {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    HasLogDeg f 0 ↔ IsIso f := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨a, f', h1, h2⟩ := hf
    have hs : Function.Surjective (f.app (N + a)) :=
      (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A (N + a)) (H.A (N + a)) (f.app (N + a))).2
        ((hN (N + a) (Nat.le_add_right N a)).trans (pow_zero p))
    set f'' : H ⟶ G := (p : ℤ_[p]) ^ N • f' with hf''
    have e1 : f ≫ f'' = (p : ℤ_[p]) ^ (N + a) • 𝟙 G := by
      rw [hf'', Linear.comp_smul, h1, smul_smul, ← pow_add]
    have e2 : f'' ≫ f = (p : ℤ_[p]) ^ (N + a) • 𝟙 H := by
      rw [hf'', Linear.smul_comp, h2, smul_smul, ← pow_add]
    have hc : f''.conv (N + a) = 1 := by
      have h3 : precomp (H.A (N + a)) (f.app (N + a)) (f''.conv (N + a)) =
          precomp (H.A (N + a)) (f.app (N + a)) 1 := by
        rw [map_one, ← comp_conv_left, e2, pow_smul_conv]
      refine WithConv.ofConv_injective (BialgHom.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hs x
      exact DFunLike.congr_fun (congrArg WithConv.ofConv h3) y
    obtain ⟨g, hg⟩ := GlobalTheory.T.pDivHom_divisible_by_pow_of_kills_pow_torsion p k H G (N + a) f'' hc
    refine ⟨⟨g, ?_, ?_⟩⟩
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.comp_smul, ← hg, e1]
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.smul_comp, ← hg, e2]
  · intro hi
    refine ⟨0, fun n _ => ?_⟩
    rw [pow_zero]
    refine (GlobalTheory.T.bialgHom_surjective_iff_finrank_kernelQuotient_eq_one k (G.A n) (H.A n) (f.app n)).1 fun x => ⟨(inv f).app n x, ?_⟩
    have h := congrArg (fun φ : G ⟶ G => φ.app n x) (IsIso.hom_inv_id f)
    exact h

theorem isog_basics : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k),
    (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧
    ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) :=
  fun _ _ _ _ _ G => ⟨fun m => ⟨isIsog_pow_smul_id G m, hasLogDeg_pow_smul_id G m⟩,
    fun _ _ _ _ => isIsog_comp, fun _ _ _ _ => isIsog_of_comp,
    fun _ f => hasLogDeg_zero_iff_isIso f⟩

end

end GlobalTheory.Dieu
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChernClause

theorem pchern_of (hsep : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated)
 (hcharts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k))
 (hpull : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
 (hframe : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k))
 (hlift : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J))
 (halg : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg))
 (hcup : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc) (β : Λ → Λ → Hol F.V), (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) → ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg))
 (hsym : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : GlobalTheory.CatCoh.C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = GlobalTheory.CatCoh.mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = GlobalTheory.CatCoh.d0 K.Oc G T T' φ) → (∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → GlobalTheory.CatCoh.mp K.Oc φ (G T) = G T') → ∃ r : Hol F.V, ∀ T, G T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l)
 (hah : ∀ {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ), H.IsHermitian → ∀ x y : Fin g → ℂ, (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) = (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((x ⬝ᵥ H.mulVec (star y)).im : ℂ))
 (h1 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T))
 (h0 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p) : PChern (-1) := by
  intro A _ g hA L u P hP M u' hM hex H χ ψ hAH hψ x x'
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  obtain ⟨K, r, j, hR, hS, hF, hj⟩ := hcharts (fibUnif u) (hsep A hA) M.U hM.cover
  have hB : K.Based := by
    obtain ⟨k, hk⟩ := hR.1 (0, 0) trivial
    exact ⟨k, fun z _ ↦ by rwa [Subsingleton.elim z 0]⟩
  obtain ⟨i, uu, ℓ, hi, huu, hℓ, hz⟩ := hpull K r M j hj _ hc
  obtain ⟨fr, af, lg, f1, f2, a1, a2, a3, a4, a5⟩ := hframe A L u M u' hM hex H χ hAH K r hF j hj
  obtain ⟨e, he⟩ := hlift K r M hM j hj fr af f1 f2 i hi uu huu
  let β : u.Λ → u.Λ → ℂ := fun l m ↦ (Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  obtain ⟨c, hcc⟩ := halg K af lg (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) a1 a2 a3 a4 a5 e uu ℓ.1 he hℓ
  let pr : primDR A → (u.Λ →+ Hol (fibFam u).V) := fun c ↦
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by rw [map_add (f := _), LinearMap.add_apply, (algebraMap ℂ (Hol (fibFam u).V)).map_add] }
  have hpr : ∀ c : primDR A, r.coef.pull1 c.1 = K.perCl (pr c) := fun c ↦ hP c K r hF
  obtain ⟨c', hc'⟩ := hcup K (fun k ↦ pr (a k)) (fun k ↦ pr (b k)) ℓ c
    (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) (by

      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_cup, hpr, hpr]) hcc
  let δ : u.Λ → u.Λ → ℂ := fun l m ↦ ∑ k, P l (a k) * P m (b k) - β l m
  have d1 : ∀ l l' m, δ (l + l') m = δ l m + δ l' m := fun l l' m ↦ by
    simp only [δ, β, map_add (f := _), LinearMap.add_apply, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add,
      add_mul, Finset.sum_add_distrib]
    ring
  have d2 : ∀ l m m', δ l (m + m') = δ l m + δ l m' := fun l m m' ↦ by
    simp only [δ, β, map_add (f := _), LinearMap.add_apply, Submodule.coe_add, add_dotProduct,
      mul_add, Finset.sum_add_distrib]
    ring
  let β' : u.Λ →+ u.Λ →+ Hol (fibFam u).V := AddMonoidHom.mk'
    (fun l ↦ AddMonoidHom.mk' (fun m ↦ algebraMap ℂ (Hol (fibFam u).V) (δ l m)) fun m m' ↦ by rw [d2, (algebraMap ℂ (Hol (fibFam u).V)).map_add])
    fun l l' ↦ AddMonoidHom.ext fun m ↦ by
      change algebraMap ℂ (Hol (fibFam u).V) (δ (l + l') m) = algebraMap ℂ (Hol (fibFam u).V) (δ l m) + algebraMap ℂ (Hol (fibFam u).V) (δ l' m)
      rw [d1, (algebraMap ℂ (Hol (fibFam u).V)).map_add]
  have hs := hsym K (fun c hc ↦ h1 K hR hB c hc) (fun G hG ↦ h0 K hR G fun T T' φ h ↦ (hG T T' φ h).symm) hS hR β' c'
    (fun T T' T'' φ ψ ↦ by
      rw [hc']
      congr 1
      change _ = algebraMap ℂ (Hol (fibFam u).V) (δ φ.deg ψ.deg)

      simp only [δ, map_sub, map_sum, map_mul]
      rfl) x x'
  have hs' : δ x x' = δ x' x := by
    have := congrArg (Hol.ev (W := (fibFam u).V) 0 trivial) hs
    change Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x x')) = Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x' x)) at this
    simpa using this
  rw [wedgeForm_apply, ← hah H hAH.1 x x', Finset.sum_sub_distrib]
  simp only [δ, β] at hs'
  have e2 : ∑ k, P x (b k) * P x' (a k) = ∑ k, P x' (a k) * P x (b k) := Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [e2]
  linear_combination hs'

theorem pchern : GlobalTheory.AnPer.PChern (-1) :=
  pchern_of @_root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base @_root_.GlobalTheory.T.exists_translationClosed_charts_subordinate_to_cover @_root_.GlobalTheory.T.isCrystallineChern_on_analytic_thickenings @_root_.GlobalTheory.T.exists_frame_factorOfAutomorphy_log @_root_.GlobalTheory.T.exists_units_comparing_lifted_transitions_factor @_root_.GlobalTheory.T.log_cocycle_cohomologous_alt @_root_.GlobalTheory.T.cup_period_classes_sum_const @_root_.GlobalTheory.T.const_biadditive_coboundary_symmetric @GlobalTheory.pi_mul_hermitian_alternation @_root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based @_root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible

end GlobalTheory.AnPer.ChernClause
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
end

section

open GlobalTheory.AnPer

theorem _root_.GlobalTheory.T.exists_integrationOverCyclesHom : PHom := by
  first | exact @GlobalTheory.AnPer.pHom | exact GlobalTheory.AnPer.pHom | (intros; apply GlobalTheory.AnPer.pHom <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fibrePeriod_eq_familyPeriod_value : PFix := by
  first | exact @GlobalTheory.AnPer.period_fibre_eq_value | exact GlobalTheory.AnPer.period_fibre_eq_value | (intros; apply GlobalTheory.AnPer.period_fibre_eq_value <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integrationOverCycles_lifts_lieLattice : PLie := by
  first | exact @GlobalTheory.AnPer.pLie_holds | exact GlobalTheory.AnPer.pLie_holds | (intros; apply GlobalTheory.AnPer.pLie_holds <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deRhamHypercohomologyOne_baseChange_flat_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  first | exact @GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | exact GlobalTheory.liftSemi_pullHyp1_bijective_of_finite | (intros; apply GlobalTheory.liftSemi_pullHyp1_bijective_of_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

theorem _root_.GlobalTheory.T.dividedWeight_nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  first | exact @GlobalTheory.MeanTop.nodes_far_and_spread | exact GlobalTheory.MeanTop.nodes_far_and_spread | (intros; apply GlobalTheory.MeanTop.nodes_far_and_spread <;> assumption)
end
