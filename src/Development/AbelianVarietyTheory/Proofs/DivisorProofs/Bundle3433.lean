module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle017
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem exists_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀
  obtain ⟨red, hfin, hproj, hsurj, hker, hcorr, hpush, E', M', hE'M', hE'⟩ :=
    GlobalTheory.CrysRed.exists_crysRed C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  haveI := hfin
  haveI := hproj
  obtain ⟨φ₀, hφ₀, huniq, hadj, φ', hφ', hrel⟩ := GlobalTheory.HTDefLift.exists_crysForm p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨hskew, hbij⟩ := GlobalTheory.HTPerf.skew_bijective p D R b N C C₀ π hπ hsq tR o₀ φ₀ hφ₀
  haveI : Nontrivial C₀ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have ht : RingHom.ker π = ⊤ := eq_top_iff.2 fun x _ ↦ RingHom.mem_ker.2 (Subsingleton.elim _ _)
    rw [ht, ← Ideal.one_eq_top, one_pow] at hsq
    exact one_ne_zero hsq
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  have hlagr := GlobalTheory.HTLagr.fil_lagrangian p D R b N C₀ _ o₀ φ' (GlobalTheory.AbelianDim.exists_relDim C₀ o₀.A o₀.ab) hφ'
  have hlie := GlobalTheory.HTSummand.lie_mod_fil p D R b N C₀ (π.comp tR) _ (GlobalTheory.Cris.spMap_comp tR π).symm o₀
  have hprojF := GlobalTheory.T.crystal_projective_over_tensor_ringOfIntegers D.F C C₀ π hπ hsq o₀.A o₀.ab D.O o₀.act
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  let F : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A) := (Fil o₀.A).comap red
  have hredI : ∀ x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), red x = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr n _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · rw [LinearMap.map_smulₛₗ, RingHom.mem_ker.1 hr, zero_smul]
    · rw [map_add (f := _), hx, hy, add_zero]
  have hIF : RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) ≤ F := fun x hx ↦ by
    show red x ∈ Fil o₀.A
    rw [hredI x hx]; exact zero_mem _
  have hFstab : ∀ (c : D.O), ∀ x ∈ F, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act c x ∈ F := by
    intro c x hx
    show red _ ∈ Fil o₀.A
    rw [hpush]
    haveI := o₀.act.hom c
    exact push_mem_Fil (o₀.act.act c) hx
  have hFiso : ∀ x ∈ F, ∀ y ∈ F, φ₀ x y ∈ RingHom.ker π := by
    intro x hx y hy
    rw [RingHom.mem_ker, ← hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact hlagr.1 _ hx _ hy
  have hFlagr : ∀ x, (∀ y ∈ F, φ₀ x y ∈ RingHom.ker π) → x ∈ F := by
    intro x hx
    show red x ∈ Fil o₀.A
    refine hlagr.2 _ fun z hz ↦ ?_
    obtain ⟨y, rfl⟩ := hsurj z
    rw [hrel x (red x) y (red y) ((hcorr _ _).2 rfl) ((hcorr _ _).2 rfl)]
    exact RingHom.mem_ker.1 (hx y hz)
  have hE'F : E' ⊔ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)) = F := by
    refine le_antisymm (sup_le (fun d hd ↦ (hE' _).2 ⟨d, hd, rfl⟩) hIF) fun x hx ↦ ?_
    obtain ⟨d, hd, he⟩ := (hE' (red x)).1 hx
    have hx' : x = d + (x - d) := by abel
    rw [hx']
    exact Submodule.add_mem_sup hd (hker _ (by rw [map_sub, he, sub_self]))
  have hFlie : ∀ d, GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d ∈ F →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F),
        GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - tR (b.t i c) • w i ∈ F) ∧
        d - ∑ i, w i ∈ F := by
    intro d hd
    have hd' : red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) d - tR b.ρ • d)
        ∈ Fil o₀.A := hd
    rw [map_sub, LinearMap.map_smulₛₗ, hpush] at hd'
    obtain ⟨w₀, hw₀, hsum⟩ := hlie (red d) hd'
    choose w hw using fun i ↦ hsurj (w₀ i)
    refine ⟨w, fun i c ↦ ?_, ?_⟩
    · show red _ ∈ Fil o₀.A
      rw [map_sub, LinearMap.map_smulₛₗ, hpush, hw]
      exact hw₀ i c
    · show red _ ∈ Fil o₀.A

      rw [map_sub, map_sum]
      simp only [hw]
      exact hsum
  obtain ⟨E, ⟨M, hEM⟩, hEF, hstab, hiso, hlieE⟩ := GlobalTheory.T.exists_lagrangian_lift_lie_squareZero_harrisTaylor p D R b C (RingHom.ker π) hI2 tR
    (Crys (divided₂ hsq) (spMap π) o₀.A) (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) o₀.act) hprojF φ₀ hskew hbij hadj
    F hIF hFstab hFiso hFlagr ⟨E', M', hE'M', hE'F⟩ hFlie
  refine ⟨E, ⟨M, hEM⟩, fun y ↦ ⟨fun hy ↦ ?_, fun ⟨d, hd, hc⟩ ↦ ?_⟩, fun c d hd ↦ hstab c d hd,
    fun φ hφ x hx y hy ↦ by rw [huniq φ hφ]; exact hiso x hx y hy, fun d hd ↦ hlieE d hd⟩
  · obtain ⟨x, rfl⟩ := hsurj y
    have hx : x ∈ F := hy
    rw [← hEF] at hx
    obtain ⟨d, hd, j, hj, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨d, hd, (hcorr _ _).2 (by rw [map_add (f := _), hredI j hj, add_zero])⟩
  · rw [← (hcorr d y).1 hc]
    have : d ∈ F := hEF ▸ Submodule.mem_sup_left hd
    exact this

end GlobalTheory.HTSummand
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_tjCorr_finiteEtale : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c hw hu hj hc hm M
  haveI : LocallyOfFiniteType M.s := by
    haveI : Smooth M.s := M.smooth.smooth
    infer_instance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, o₀, m₀, o', ψ, hfin, het, hisog, htj, huniv⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N hN hNp hp r w j c hw hu hj hc hm M.X M.s M.univ
  obtain ⟨t, ⟨ht, ⟨mt⟩⟩, -⟩ := M.rep Y.left (Y.hom ≫ M.s) o'
  obtain ⟨h3, h4⟩ := GlobalTheory.T.harrisTaylor_typeTj_correspondence_target_finite_etale p D R b N hN hNp hp r w j c hw hu hj hc hm M Y.left Y.hom t ht.symm o₀ o' m₀ mt ψ
    hisog htj hfin het huniv
  have hsurj : Surjective Y.hom := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X x
    obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp k) M.s a M.univ
    obtain ⟨o₁', ψ₁, h1, h2⟩ := GlobalTheory.T.harrisTaylor_exists_typeTj_pIsogeny p D R b N hN hNp hp r w j c hw hu hj hc hm k (a ≫ M.s) o₁
    obtain ⟨y, ⟨hy, -⟩, -⟩ := huniv (Sp k) a o₁ o₁' m ψ₁ h1 h2
    have hx : x ∈ Set.range a.base := by rw [ha]; rfl
    obtain ⟨z', rfl⟩ := hx
    exact ⟨y.base z', by rw [← hy]; rfl⟩
  let T : TjCorr M.toRepFam r w j c :=
    { Y := Y.left, s := Y.hom, t := t, st := ht.symm, o := o₀, o' := o', ms := m₀, mt := mt, ψ := ψ,
      isog := hisog, tj := htj, wPrime := hw.isPrime, uLe := hu,
      pReg := fun U f hf => pReg_of_isUnit (Y.hom ≫ M.s) hp U f hf, sFin := hfin, tFin := h3, sSurj := hsurj }
  exact ⟨T, hfin, het, hsurj, h3, h4, fun S x o₁ o₁' m ψ₁ _ h1 h2 => huniv S x o₁ o₁' m ψ₁ h1 h2⟩

end GlobalTheory.UPel.HT.ES
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.finite_points_closure_genericCorrespondence_snd : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∀ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s → gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ → IsFinite gs → Etale gs → IsFinite gt → Etale gt → IsPIsog c o₀ o₀' ψ₀ → IsTj r w j o₀ o₀' ψ₀ → ∀ z : M.X, {u : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvrPartners_snd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaPullback

theorem theta_pull_O1_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)) (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)) := by
  intro E _ _ _ H Dw l Xo c o _ m n f hodd hm hunit hn hth Y g hg hdet
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (↥c.F) N
  haveI : IsProper Y.s := by rw [← hs]; infer_instance
  have hvb := (GlobalTheory.T.modelSemiAbelian_relDim_cotangent_vectorBundle E H Dw l Xo c Y).2
  have hO : ((ProjSpace.O1 o n).pull g).IsLB := LB.isLB_pull (ProjSpace.O1_isLB o n) g
  have hA : (lbPow ((ProjSpace.O1 o n).pull g) (8 * (n + 1).factorial)).IsLB := LB.isLB_linComb hO _ _
  have hB : (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
      (4 * (n + 1).factorial * (n + 1).factorial)).IsLB := LB.isLB_linComb hvb.isLB_det _ _
  have hC : (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial)).IsLB :=
    LB.isLB_linComb hdet _ _
  have hAB := GlobalTheory.T.lineBundleIso_of_iso_on_rational_model_components (↥c.F) Y.X Y.s _ _ Y.normal inferInstance inferInstance inferInstance hA hB
    (fun Ω _ _ M io hio hio' => GlobalTheory.T.theta_map_pull_O1_power_hodge E H Dw l Xo c o m n f hodd hm hunit hn hth Y g hg Ω M io hio hio')
  have hCB : LBIso (lbPow (GlobalTheory.FlagMod.detOm Y) (4 * (n + 1).factorial * (n + 1).factorial))
      (lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)))
        (4 * (n + 1).factorial * (n + 1).factorial)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (GlobalTheory.T.detInvariantDiff_iso_hodgeLineBundle E H Dw l Xo c Y hdet) _ _
  exact LBIso.trans hA hB hC hAB hCB.symm

end GlobalTheory.ThetaPullback
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AmpleStep

variable {X : Scheme.{0}} [IsIntegral X]

theorem generatesAt_add_vanishesAt {D : CartierDiv X} {x : X} {f u : X.functionField}
    (hf : D.GeneratesAt x f) (hu : D.VanishesAt x u) : D.GeneratesAt x (f + u) := by
  obtain ⟨e, he⟩ := D.exists_isEqn x
  rw [he.generatesAt_iff] at hf ⊢
  rw [he.vanishesAt_iff] at hu
  obtain ⟨a, ha, hae⟩ := hf
  obtain ⟨b, hb, hbe⟩ := hu
  refine ⟨a + b, ?_, by rw [map_add (f := _), hae, hbe, add_mul]⟩
  by_contra hn
  have h1 : a + b ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h2 : a ∈ IsLocalRing.maximalIdeal _ := by
    have := Ideal.sub_mem _ h1 hb
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

theorem eff_nsmul {D : CartierDiv X} (hD : D.Eff) (r : ℕ) : (r • D).Eff := by
  induction r with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ r ih => rw [succ_nsmul]; exact ih.add hD

variable [IsLocallyNoetherian X]

theorem mult_nsmul (E : CartierDiv X) (r : ℕ) (z : X) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero =>
    have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h₀
    rw [zero_nsmul]
    push_cast
    omega
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

end GlobalTheory.AmpleStep


open GlobalTheory.AmpleStep in
theorem GlobalTheory.AmpleStep.exists_divisor : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (m : ℕ) (G A : CartierDiv X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB (toLB A) →
      IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k →
      topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h →
      (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) →
      ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p (toLB A) h B ∧ Off B z ∧
        (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧
        (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hP X _ _ _ p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.GeneralLift.exists_lift_klt hP X p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l, hll, hhl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hnk⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hP X p n hp hn Δ m G A D P z k h hΔ hklt hm hG hA hD hPz hk hdim hz hh hnum l₁
  obtain ⟨u, hu, huz, hukl⟩ := hl₁ l hll f₀ hf₀
  have hgz : (l • A).GeneratesAt z (f₀ + u) := generatesAt_add_vanishesAt hgen huz
  let g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgz.ne_zero
  have hgv : (g : X.functionField) = f₀ + u := rfl
  have hEeff : (CartierDiv.principal g + l • A).Eff :=
    CartierDiv.mem_sections_iff_eff.1 (hgv ▸ Submodule.add_mem _ hf₀ hu)
  have hl0 : (0 : ℚ) < l := hh.trans hhl
  have hlpos : 0 < l := by exact_mod_cast hl0
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_,
    fun δ hδ hδ' x hx => hnk u hu huz g hgv δ hδ hδ' x hx, ?_⟩
  · obtain ⟨a, b, ha0, hb0, hab⟩ : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ h = a / b := by
      have hnum0 : 0 < h.num := Rat.num_pos.2 hh
      refine ⟨h.num.toNat, h.den, by omega, h.den_pos, ?_⟩
      have e1 : ((h.num.toNat : ℕ) : ℚ) = (h.num : ℚ) := by
        have : ((h.num.toNat : ℕ) : ℤ) = h.num := Int.toNat_of_nonneg hnum0.le
        exact_mod_cast this
      rw [e1, Rat.num_div_den]
    refine ⟨b * l, a • (CartierDiv.principal g + l • A), Nat.mul_pos hb0 hlpos, eff_nsmul hEeff a,
      ?_, fun C hC => ?_⟩
    · funext x
      simp only [Pi.smul_apply, smul_eq_mul, qWeil, mult_nsmul, hab]
      push_cast
      field_simp
    · have hcls : cls (toLB (a • (CartierDiv.principal g + l • A))) (isLB_toLB _) =
          (a * l) • cls (toLB A) (isLB_toLB A) + 0 • cls (toLB A) (isLB_toLB A) := by
        rw [← toPic_apply, ← toPic_apply]
        simp [map_nsmul, toPic_principal, smul_smul, mul_comm]
      have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ _ _ (isLB_toLB _) (isLB_toLB A)
        (isLB_toLB A) (a * l) 0 C hC hcls
      rw [e, hab]
      push_cast
      field_simp
      ring
  · have hoff : Off (qWeil (CartierDiv.principal g + l • A) 1) z :=
      (off_qWeil_iff_notMem_supp X _ 1 z hEeff one_pos).2 (by
        obtain ⟨e, he⟩ := (l • A).exists_isEqn z
        rw [CartierDiv.notMem_supp_iff, ((CartierDiv.isEqn_principal g z).add he).generatesAt_iff,
          one_mul, Units.val_mul, hgv]
        exact (he.generatesAt_iff).1 hgz)
    intro w hw
    simp [hoff w hw]
  · intro y hy a ha hk'
    exact hukl g hgv y hy a (h / l) ha ((div_lt_one hl0).2 hhl) hk'
end
end

section


theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  first | exact @GlobalTheory.HSNef.ampleHS_of_principalisation | exact GlobalTheory.HSNef.ampleHS_of_principalisation | (intros; apply GlobalTheory.HSNef.ampleHS_of_principalisation <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem qNum_principal_add_nsmul {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) {N : LB X} (hN : IsAmpleLB N) {A : CartierDiv X} (e : toPic A = cls N hN.isLB)
    (l : ℕ) {g : X.functionFieldˣ} (hg : (g : X.functionField) ∈ (l • A).sections) :
    QNum p N l (qWeil (CartierDiv.principal g + l • A) 1) := by
  letI := algebraΓOfHom p
  refine ⟨1, CartierDiv.principal g + l • A, one_pos, CartierDiv.mem_sections_iff_eff.1 hg, rfl, ?_⟩
  intro C hC
  have e1 : toPic (CartierDiv.principal g + l • A) = l • cls N hN.isLB := by
    rw [map_add (f := _), map_nsmul, toPic_principal, e, zero_add]
  have e2 : cls (toLB (CartierDiv.principal g + l • A)) (isLB_toLB _) =
      cls (lbPow N l) (isLB_lbPow hN.isLB l) := by
    rw [← toPic_apply, e1, GlobalTheory.CechPic.cls_lbPow hN.isLB]
  rw [interNumRed_one_congr _ _ e2 C, hC.interNumRed_lbPow hN hN.isLB l]
  push_cast
  ring

theorem exists_step_divisor : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h → (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N : ℤ) → ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p N h B ∧ Off B z ∧ (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧ (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  intro hPr _ _ X _ _ _ p n hproj hdim Δ m G N D P z k h hΔ hklt hm hG hN hD hP hk hZ hz hh hnum
  letI := algebraΓOfHom p
  obtain ⟨A, hA⟩ := toPic_surjective (X := X) (cls N hN.isLB)
  have hAN : cls (toLB A) (isLB_toLB A) = cls N hN.isLB := by rw [← toPic_apply, hA]
  have hAamp : IsAmpleLB (toLB A) :=
    (isAmpleLB_congr (isLB_toLB A) hN.isLB ((GlobalTheory.CechPic.cls_eq_iff _ _).1 hAN)).2 hN
  have hcongr : (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A) =
      interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N := by
    rw [interNumRed_def, interNumRed_def, interNumSub_def, interNumSub_def, interNumOn_def,
      interNumOn_def]
    exact interNum_congr_cls (k := ℂ) (F := _) (fun _ => isLB_toLB A) (fun _ => hN.isLB)
      fun _ => hAN
  have hnumA : (P.card : ℚ) * (k : ℚ) ^ k <
      h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => toLB A : ℤ) := by
    rw [hcongr]; exact hnum
  obtain ⟨l₁, hl₁⟩ :=
    GlobalTheory.GeneralLift.exists_lift_klt hPr X p n hproj hdim Δ D m G A z hm hG hD hAamp
  obtain ⟨l, hll, hl, f₀, hf₀, hgen, δ₀, hδ0, hδ1, hmain⟩ :=
    GlobalTheory.T.exists_global_section_angehrnSiu_inductive_step hPr X p n hproj hdim Δ m G A D P z k h hΔ hklt hm hG hAamp hD hP hk hZ hz hh
      hnumA l₁
  obtain ⟨u, hu, hvan, hoff⟩ := hl₁ l hll f₀ hf₀
  have hgen' : (l • A).GeneratesAt z (f₀ + u) :=
    GlobalTheory.Cartier.CommonEqn.generatesAt_add hgen hvan
  set g : X.functionFieldˣ := Units.mk0 (f₀ + u) hgen'.ne_zero with hg_def
  have hgval : (g : X.functionField) = f₀ + u := rfl
  have hgmem : (g : X.functionField) ∈ (l • A).sections := by
    rw [hgval]; exact add_mem hf₀ hu
  have hlpos : (0 : ℚ) < l := lt_trans hh hl
  have hEff : (CartierDiv.principal g + l • A).Eff := CartierDiv.mem_sections_iff_eff.1 hgmem
  have hzs : z ∉ (CartierDiv.principal g + l • A).supp := by
    rw [CartierDiv.notMem_supp_iff]
    have h1 : (CartierDiv.principal g).GeneratesAt z (g : X.functionField)⁻¹ :=
      CartierDiv.isEqn_iff_generatesAt_inv.1 (CartierDiv.isEqn_principal g z)
    have h2 : (l • A).GeneratesAt z (g : X.functionField) := by rw [hgval]; exact hgen'
    have h3 := h1.mul h2
    rwa [inv_mul_cancel₀ (Units.ne_zero g)] at h3
  refine ⟨(h / l) • qWeil (CartierDiv.principal g + l • A) 1, δ₀, hδ0, hδ1, ?_, ?_, ?_, ?_⟩
  · have h1 := qNum_principal_add_nsmul p hN hA l hgmem
    have h2 := qNum_smul X p hproj N (l : ℚ) (h / l) _ (div_nonneg hh.le hlpos.le) h1
    rwa [div_mul_cancel₀ h hlpos.ne'] at h2
  · intro w hw
    have h0 := (off_qWeil_iff_notMem_supp X (CartierDiv.principal g + l • A) 1 z hEff one_pos).2 hzs
    rw [Pi.smul_apply, h0 w hw, smul_zero]
  · intro δ h0 h1 x hx
    exact hmain u hu hvan g hgval δ h0 h1 x hx
  · intro y hy a ha hka
    exact hoff g hgval y hy a (h / l) ha ((div_lt_one hlpos).2 hl) hka

end GlobalTheory.PairStep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ X₁ : Setup F W8 i, ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_model_divisor_of_orders | exact GlobalTheory.Poinc.exists_model_divisor_of_orders | (intros; apply GlobalTheory.Poinc.exists_model_divisor_of_orders <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
end
