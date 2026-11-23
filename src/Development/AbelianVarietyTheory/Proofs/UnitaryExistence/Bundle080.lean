module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle074
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle075
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem exists_algebraMap_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : R ⊗[F] E) (hz : sigR R σ z = z) :
    ∃ a : R, algebraMap R (R ⊗[F] E) a = z := by
  have hT : ∀ z : R ⊗[F] E, ∃ t : R, z + sigR R σ z = t ⊗ₜ 1 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a x =>
      obtain ⟨t, ht⟩ := htr x
      refine ⟨t • a, ?_⟩
      have h : sigR R σ (a ⊗ₜ x) = a ⊗ₜ σ x := by simp [sigR]
      rw [h, ← TensorProduct.tmul_add, ← ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t', ht'⟩ := hy
      refine ⟨t + t', ?_⟩
      rw [map_add (f := _), TensorProduct.add_tmul, ← ht, ← ht']; ring
  obtain ⟨t, ht⟩ := hT z
  refine ⟨(2 : F)⁻¹ • t, ?_⟩
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← TensorProduct.smul_tmul', ← ht, hz, ← two_smul F z, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_unit_of_sigR_fixed {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (htr : ∀ x : E, ∃ t : F, algebraMap F E t = x + σ x) (z : (R ⊗[F] E)ˣ)
    (hz : sigR R σ (z : R ⊗[F] E) = z) :
    ∃ a : Rˣ, Units.map (algebraMap R (R ⊗[F] E)).toMonoidHom a = z := by
  have hz' : sigR R σ ((z⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (z⁻¹ : (R ⊗[F] E)ˣ) := by
    apply z.isUnit.mul_left_cancel
    conv_lhs => rw [← hz, ← map_mul]
    simp
  obtain ⟨a, ha⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz
  obtain ⟨b, hb⟩ := exists_algebraMap_of_sigR_fixed R σ htr _ hz'
  have hinj : Function.Injective (algebraMap R (R ⊗[F] E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; simp)
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, Units.ext ha⟩

theorem exists_root_of_norm_one {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ y, σ y ≠ y) (u : E) (hu : σ u * u = 1) : ∃ x : Eˣ, (x : E) = u * σ x := by
  by_cases h : 1 + u = 0
  · obtain ⟨y, hy⟩ := hne
    refine ⟨Units.mk0 (y - σ y) (sub_ne_zero.2 hy.symm), ?_⟩
    rw [Units.val_mk0, map_sub, hσ]
    linear_combination (y - σ y) * h
  · refine ⟨Units.mk0 (1 + u) h, ?_⟩
    rw [Units.val_mk0, map_add (f := _), map_one]
    linear_combination - hu

theorem isDetRoot_mul {D : D7} (V : HSp D) (g g' : GA D V) (x x' : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hx' : IsDetRoot V g' x') : IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [hx, hx']
  ring

theorem isDetRoot_laws : ∀ (D : D7) (V : HSp D), (∀ g : GA D V, ∃ x, IsDetRoot V g x) ∧ (∀ g x x', IsDetRoot V g x → IsDetRoot V g x' → ∃ a, x' = x * idF D a) ∧ (∀ γ ∈ GQ V, ∃ x : D.host.Eˣ, IsDetRoot V γ (Units.map (incA D).toMonoidHom x)) ∧ ∀ g g' x x', IsDetRoot V g x → IsDetRoot V g' x' → IsDetRoot V (g * g') (x * x') := by
  intro D V
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  refine ⟨GlobalTheory.RecDict.exists_isDetRoot D V, ?_, ?_, ?_⟩
  · intro g x x' hx hx'
    have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      intro x
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add (f := _), hσ, add_comm]
    unfold IsDetRoot at hx hx'
    obtain ⟨a, ha⟩ := exists_unit_of_sigR_fixed (AF D.host.F) D.sp.cm.sig htr (x⁻¹ * x') (by
      apply (x.isUnit.map (sigR (AF D.host.F) D.sp.cm.sig)).mul_left_cancel
      apply x.isUnit.mul_left_cancel
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel_left, mul_left_comm, ← Units.val_mul, mul_inv_cancel_left]
      linear_combination (sigR (AF D.host.F) D.sp.cm.sig (x' : AE D)) * hx -
        (sigR (AF D.host.F) D.sp.cm.sig (x : AE D)) * hx')
    refine ⟨a, ?_⟩
    unfold idF
    rw [ha, mul_inv_cancel_left]
  · intro γ hγ
    obtain ⟨γ', -, hγ'⟩ := hγ
    have hdet : (Formalism.L2.Theta.mt V γ).det = incA D (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det := by
      rw [RingHom.map_det]
      congr 1
      exact congrArg Units.val hγ'.symm
    have hc : ∀ y, cA D (incA D y) = incA D (D.sp.cm.sig y) := by
      intro y; simp [cA, sigR, inclR]
    have hinj : Function.Injective (incA D) :=
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
    have hu := det_conj_mul V γ
    rw [hdet, hc, ← map_mul, ← map_one (incA D)] at hu
    obtain ⟨x, hx⟩ := exists_root_of_norm_one (D.sp.cm.sig : D.host.E →+* D.host.E) hσ
      (GlobalTheory.RecDict.cmData_sig_ne_id D.sp.cm) _ (hinj hu)
    refine ⟨x, ?_⟩
    have key : incA D (x : D.host.E) = (Formalism.L2.Theta.mt V γ).det * cA D (incA D (x : D.host.E)) := by
      rw [hdet, hc, ← map_mul]
      exact congrArg _ hx
    unfold IsDetRoot
    rw [Units.coe_map]
    exact key
  · exact isDetRoot_mul V

end GlobalTheory.Member
end

section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem framedPoint_field_fromTest :
    Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
      (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), SpreadSt Xo c := by
  intro hB E _ _ _ H Dw l Xo c S _ _ y
  let xF : Sp S ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])
  have h1 : xF ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  have h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _
  let q : Sp S := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S)
  obtain ⟨p, j, y₀, hj, hq⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hB E H Dw l Xo c (xF q)
  obtain ⟨g, hg, hfac⟩ := openChart_factor_near_prime E H Dw l Xo c p.R j y₀ hj S xF h2 q hq
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem _)
  obtain ⟨ψ, hψ⟩ := hfac S (AlgHom.id c.F S) (Ne.isUnit hg0)
  have hid : spMap (AlgHom.id c.F S).toRingHom = 𝟙 (Sp S) := Spec.map_id _
  rw [hid, Category.id_comp] at hψ
  have hx : y.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [← h1, hψ, Category.assoc, hj.2.1]
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hB E H Dw l Xo c p y₀
  obtain ⟨a, ⟨-, ha⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hB E H Dw l Xo c p.R A.R y₀ π X s u hu S y ψ hx
  exact ⟨A, a, u, ha⟩

end GlobalTheory.Frames
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.AbelianNoTorsion

theorem finite_points_of_no_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 2 ≤ n → (n : k) ≠ 0 → (∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ^ n = 1 → x = 1) → Finite (𝟙_ (Over (Sp k)) ⟶ A) := by
  intro k _ _ A _ hA n hn hnk htor
  obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  have hpk : (p : k) ≠ 0 := fun h => hnk (by rw [Nat.cast_mul, h, zero_mul])
  have hfin : Finite (⊤ : Subgroup (𝟙_ (Over (Sp k)) ⟶ A)) :=
    GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion GlobalTheory.abMulN_holds k A p hA hp hpk ⊤ Set.univ
      isClosed_univ (fun x => ⟨fun _ => Set.subset_univ _, fun _ => Subgroup.mem_top x⟩)
      (fun x _ hx => htor x (by rw [pow_mul, hx, one_pow]))
  exact Finite.of_equiv _ Subgroup.topEquiv.toEquiv

end GlobalTheory.AbelianNoTorsion
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.TransvLevel

theorem herm_smul_left {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem transv_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (m : ℕ), IsIntegral ℤ ((m : E) * (2 * X.ξ0)) → ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ X.Γ, ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((((X.g * X.NA * X.NC * m : ℕ) : ℝ) : ℂ) * τ.1 b) := by
  intro E _ _ _ r X m hm v hv hiso b hb hbi
  have hξ' : IsCMField.complexConj E X.ξ0 = -X.ξ0 := X.ξ0_im
  have hκc : IsCMField.complexConj E X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h <;> simp [h, hξ', map_ofNat]
  have hb' : IsCMField.complexConj E b = b := hb
  have hmκ : IsIntegral ℤ ((m : E) * X.κ0) := by
    rcases X.κ0_xi with h | h
    · rw [h]; exact hm
    · rw [h, mul_neg]; exact hm.neg
  set α : E := ((X.g * X.NA * X.NC * m : ℕ) : E) * b * X.κ0 with hαdef
  have hα : cc α = -α := by
    simp [hαdef, cc, hb', hκc]
  have key : ∀ x ∈ X.Λ,
      (b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v) ∈ X.Λ := fun x hx =>
    GlobalTheory.FlagData.smul_mem_of_isIntegral _
      ((hbi.mul hmκ).mul (X.L'_int _ (X.NA_sub x hx) _ hv)) (X.NC_sub v hv)
  have e : ∀ x, (α * herm X.Gm x v) • v =
      (X.g : E) • ((b * ((m : E) * X.κ0) * herm X.Gm ((X.NA : E) • x) v) • ((X.NC : E) • v)) := by
    intro x
    rw [smul_smul, smul_smul, hαdef, herm_smul_left]
    congr 1
    push_cast
    ring
  have key' : ∀ x ∈ X.Λ, (α * herm X.Gm x v) • v ∈ X.Λ := fun x hx => by
    rw [e]
    exact GlobalTheory.FlagData.smul_mem_of_isIntegral _ (isIntegral_natCast _) (key x hx)
  refine ⟨GlobalTheory.FlagData.transv X.Gm hiso α, X.cong _
    ⟨GlobalTheory.FlagData.herm_transvMat X.Gm_herm hiso hα, fun x => ?_⟩ (fun x hx => ?_), fun τ => ?_⟩
  · change x ∈ X.Λ ↔ transvMat X.Gm v α *ᵥ x ∈ X.Λ
    rw [GlobalTheory.FlagData.transvMat_mulVec]
    refine ⟨fun hx => Submodule.add_mem _ hx (key' x hx), fun hx => ?_⟩
    have h := key' _ hx
    rw [GlobalTheory.FlagData.herm_add_smul_left, hiso, mul_zero, add_zero] at h
    simpa using Submodule.sub_mem _ hx h
  · refine ⟨_, key x hx, ?_⟩
    change transvMat X.Gm v α *ᵥ x - x = _
    rw [GlobalTheory.FlagData.transvMat_mulVec, add_sub_cancel_left, e]
  · change (transvMat X.Gm v α).map τ.1 = _
    refine TransvectionPeriodicity.transvMat_map X.toData v τ α _ ?_
    rw [hαdef, map_mul, map_mul, TransvectionPeriodicity.emb_kappa X.toData τ, map_natCast]
    push_cast
    ring

end GlobalTheory.TransvLevel
end
